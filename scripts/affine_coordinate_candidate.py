"""Propose concrete affine Loop candidates; all mappings require validation."""
from pathlib import Path
import argparse
import external_affine_candidate as syntax

def rewrite_body(node,depth,replace):
    def expression(value):
        if not isinstance(value,list):return value
        if value[0]=='var':return replace(value,depth)
        return [value[0],*[expression(part) for part in value[1:]]]
    kind=node[0]
    if kind=='loop':return [kind,expression(node[1]),expression(node[2]),rewrite_body(node[3],depth+1,replace)]
    if kind=='guard':return [kind,expression(node[1]),rewrite_body(node[2],depth,replace)]
    if kind=='seq':return [kind,*[rewrite_body(part,depth,replace) for part in node[1:]]]
    if kind=='instr':return [kind,node[1],[expression(arg) for arg in node[2]]]
    raise ValueError('unsupported source '+kind)

def reflect_root(source):
    assert source[0]=='loop'
    def inverse(value,depth):
        return ['scale','-1',value] if int(value[1])==depth-1 else value
    return ['loop',['sum',['scale','-1',source[2]],['constant','1']],
            ['sum',['scale','-1',source[1]],['constant','1']],rewrite_body(source[3],1,inverse)]

def skew_inner(source,factor):
    if source[0]!='loop' or source[3][0]!='loop':return None
    child=source[3]
    def inverse(value,depth):
        return ['sum',value,['scale',str(-factor),['var',str(depth-1)]]] if int(value[1])==depth-2 else value
    offset=['scale',str(factor),['var','0']]
    body=rewrite_body(child[3],2,inverse)
    return [*source[:3],['loop',['sum',child[1],offset],['sum',child[2],offset],body]]

def generate(directory,output,mode,factor=1):
    choices=[]
    for path in sorted(Path(directory).glob('*.sexp')):
        request=syntax.parse(path.read_text());fields={field[0]:field[1] for field in request[1:]};source=fields['source']
        if mode.startswith('reflect'):
            if source[0]!='loop' or source[3][0]!='loop':continue
            transformed=reflect_root(source);steps=[['reflect','0']]
        elif mode.startswith('skew'):
            transformed=skew_inner(source,factor)
            if transformed is None:continue
            steps=[['skew','1','0',str(-factor)]]
        else:raise ValueError(mode)
        if mode.endswith('wrong'):steps=[]
        choices.append(['request',path.stem,['map-index',steps,transformed]])
    assert choices;output.write_text(syntax.render(['choices',*choices])+'\n');return len(choices)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('requests',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--mode',choices=['reflect','reflect-wrong','skew','skew-wrong'],required=True)
    parser.add_argument('--factor',type=int,default=1);args=parser.parse_args()
    print('proposed',generate(args.requests,args.output,args.mode,args.factor),'untrusted candidates')

if __name__=='__main__':main()
