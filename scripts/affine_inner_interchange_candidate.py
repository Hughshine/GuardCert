"""Propose a boxed inner-axis interchange for an exported three-level source."""
from pathlib import Path
import argparse
import external_affine_candidate as syntax

def proposal(fields,wrong=False):
    headers=[];leaf=fields['source']
    while leaf[0]=='loop':headers.append(leaf[:3]);leaf=leaf[3]
    if len(headers)!=3:return None
    permutation=[0,2,1]
    def expression(node,shift=0):
        if not isinstance(node,list):return node
        if node[0]=='var':
            position=int(node[1])+shift
            if position<3:position=2-permutation.index(2-position)
            return ['var',str(position)]
        return [node[0],*[expression(part,shift) for part in node[1:]]]
    tests=[]
    for axis,(_,lower,upper) in enumerate(headers):
        coordinate=expression(['var',str(2-axis)])
        tests.extend([['le',expression(lower,3-axis),coordinate],
                      ['le',coordinate,['sum',expression(upper,3-axis),['constant','-1']]]])
    condition=tests[0]
    for test in tests[1:]:condition=['and',condition,test]
    def statement(node):
        if node[0]=='instr':return ['instr',node[1],[expression(x) for x in node[2]]]
        if node[0]=='seq':return ['seq',*[statement(x) for x in node[1:]]]
        if node[0]=='guard':return ['guard',expression(node[1]),statement(node[2])]
        raise ValueError('inner interchange leaf '+node[0])
    candidate=['guard',condition,statement(leaf)]
    for axis in reversed(permutation):
        low,high=fields['axes'][axis]
        candidate=['loop',['constant',low],['constant',high],candidate]
    return ['map-index',[] if wrong else [['swap','1']],candidate]

def parametric_proposal(fields):
    headers=[];leaf=fields['source']
    while leaf[0]=='loop':headers.append(leaf[1:3]);leaf=leaf[3]
    if len(headers)!=3:return None
    order=[0,2,1]
    def rebind(node,old_prefix,new_prefix):
        if not isinstance(node,list):return node
        if node[0]=='var':
            position=int(node[1])
            if position<len(old_prefix):
                axis=old_prefix[-1-position]
                if axis not in new_prefix:raise ValueError('bound depends on unavailable axis')
                position=len(new_prefix)-1-new_prefix.index(axis)
            else:position=position-len(old_prefix)+len(new_prefix)
            return ['var',str(position)]
        return [rebind(part,old_prefix,new_prefix) for part in node]
    try:
        candidate=rebind(leaf,[0,1,2],order)
        for index in reversed(range(3)):
            axis=order[index]
            lower,upper=[rebind(expr,list(range(axis)),order[:index]) for expr in headers[axis]]
            candidate=['loop',lower,upper,candidate]
    except ValueError:return None
    return ['map-index',[['swap','1']],candidate]

MODES=['inner-interchange','inner-interchange-parametric','interchange-tile','partition-interchange-tile',
       'wrong-first-tile','wrong-witness-tile']

def composed_proposal(fields,mode,wrong=False):
    if mode=='inner-interchange-parametric':return parametric_proposal(fields)
    first=proposal(fields,wrong or mode=='wrong-first-tile')
    if first is None or mode=='inner-interchange':return first
    axes=[fields['axes'][axis] for axis in [0,2,1]]
    tile=['tile-box-wrong' if mode=='wrong-witness-tile' else 'tile-box','2','3',axes]
    if mode=='partition-interchange-tile':
        tile=['partition-target',[['le',['var','0'],['constant','1']]],tile]
    return ['chain',first,tile]

def generate(directory,output,wrong=False,mode='inner-interchange'):
    choices=[]
    for path in sorted(Path(directory).glob('*.sexp')):
        request=syntax.parse(path.read_text());fields={x[0]:x[1] for x in request[1:]}
        candidate=composed_proposal(fields,mode,wrong)
        if candidate is not None:choices.append(['request',path.stem,candidate])
    assert choices,'no three-level affine request'
    output.write_text(syntax.render(['choices',*choices])+'\n');return len(choices)

def main():
    parser=argparse.ArgumentParser();parser.add_argument('requests',type=Path)
    parser.add_argument('output',type=Path);parser.add_argument('--wrong',action='store_true')
    parser.add_argument('--mode',choices=MODES,default='inner-interchange')
    args=parser.parse_args();print(generate(args.requests,args.output,args.wrong,args.mode),'untrusted proposals')

if __name__=='__main__':main()
