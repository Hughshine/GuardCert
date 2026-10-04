"""Construct untrusted external Loop candidates from checked request exports."""
from pathlib import Path
import argparse,re


def parse(text):
    tokens=re.findall(r'\(|\)|[^\s()]+',text); position=0
    def item():
        nonlocal position
        if position>=len(tokens):raise ValueError('unfinished request')
        token=tokens[position];position+=1
        if token==')':raise ValueError('unexpected closing parenthesis')
        if token!='(':return token
        result=[]
        while position<len(tokens) and tokens[position]!=')':result.append(item())
        if position>=len(tokens):raise ValueError('unclosed request')
        position+=1;return result
    result=item()
    if position!=len(tokens):raise ValueError('trailing request input')
    return result


def render(value):
    return '('+' '.join(map(render,value))+')' if isinstance(value,list) else value


def shift_root(source,delta):
    def expression(node,depth):
        if not isinstance(node,list):return node
        if node[0]=='var' and int(node[1])==depth-1:
            return ['sum',node,['constant',str(-delta)]]
        return [node[0],*[expression(part,depth) for part in node[1:]]]
    def statement(node,depth):
        kind=node[0]
        if kind=='loop':return [kind,expression(node[1],depth),expression(node[2],depth),statement(node[3],depth+1)]
        if kind=='guard':return [kind,expression(node[1],depth),statement(node[2],depth)]
        if kind=='seq':return [kind,*[statement(part,depth) for part in node[1:]]]
        if kind=='instr':return [kind,node[1],[expression(argument,depth) for argument in node[2]]]
        raise ValueError('unsupported source statement '+kind)
    if source[0]!='loop':raise ValueError('source has no root loop')
    return ['loop',['sum',source[1],['constant',str(delta)]],
            ['sum',source[2],['constant',str(delta)]],statement(source[3],1)]


def fission(source,reverse=False):
    def sites(node):
        if node[0]=='instr':return [node[1]]
        if node[0]=='loop':return sites(node[3])
        if node[0]=='guard':return sites(node[2])
        if node[0]=='seq':return [site for part in node[1:] for site in sites(part)]
        raise ValueError('unsupported source statement '+node[0])
    def keep(node,site):
        if node[0]=='instr':return node if node[1]==site else ['seq']
        if node[0]=='loop':return [*node[:3],keep(node[3],site)]
        if node[0]=='guard':return [*node[:2],keep(node[2],site)]
        if node[0]=='seq':return ['seq',*[keep(part,site) for part in node[1:]]]
        raise ValueError('unsupported source statement '+node[0])
    order=sites(source)
    if reverse:order.reverse()
    return ['seq',*[keep(source,site) for site in order]]


def candidate(request,mode,delta):
    assert request[0]=='affine-request'
    fields={field[0]:field[1] for field in request[1:]}
    source=fields['source']
    if mode=='identity':return source
    if mode in ['fission','reverse-fission']:return fission(source,mode=='reverse-fission')
    transformed=shift_root(source,delta)
    if mode=='drop-point':transformed[2]=['sum',transformed[2],['constant','-1']]
    steps=[] if mode=='wrong-map' else [['shift','0',str(-delta)]]
    return ['map-index',steps,transformed]


def generate(directory,output,mode,delta):
    files=sorted(directory.glob('*.sexp')); assert files,'no checked affine requests'
    choices=[['request',path.stem,candidate(parse(path.read_text()),mode,delta)] for path in files]
    output.write_text(render(['choices',*choices])+'\n')
    return len(choices)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('requests',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--mode',choices=['identity','shift-root','wrong-map','drop-point','fission','reverse-fission'],default='shift-root')
    parser.add_argument('--delta',type=int,default=1)
    args=parser.parse_args()
    print('wrote',generate(args.requests,args.output,args.mode,args.delta),'untrusted candidates')

if __name__=='__main__':main()
