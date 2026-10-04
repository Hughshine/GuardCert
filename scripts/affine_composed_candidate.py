"""Produce untrusted compositions; every stage requires kernel acceptance."""
from pathlib import Path
import argparse
import external_affine_candidate as syntax

MODES=['tile','partition-tile','partition-two-tile','shift-tile',
       'double-tile','double-tile-wrong-second','double-tile-missing-second-box',
       'wrong-first','wrong-witness','wrong-target-partition','missing-box','resource-limit']

def parameterized_address(tree,depth):
    if not isinstance(tree,list) or not tree:return False
    if tree[0]=='array':
        return any(any(int(coefficient)!=0 for coefficient in coefficients[depth:])
                   for coefficients,_ in tree[2])
    return any(parameterized_address(child,depth) for child in tree)

def proposal(fields,mode):
    source=fields['source'];depth=len(fields['axes'])
    tile=['tile-box','2','3']
    if mode.startswith('double-tile'):
        if depth!=2 or parameterized_address(fields['instructions'],depth):return None
        axes=[list(pair) for pair in fields['axes']]
        tile_axes=[[str(int(low)//width),str((int(high)+width-1)//width)]
                   for (low,high),width in zip(axes,[2,3])]
        if mode=='double-tile-missing-second-box':
            tile_axes[0][1]=str(int(tile_axes[0][0])+1)
        second='tile-box-wrong' if mode=='double-tile-wrong-second' else 'tile-box'
        return ['chain',tile,[second,'2','2',tile_axes+axes]]
    if mode in ['tile','resource-limit']:return tile
    if mode=='wrong-witness':return ['tile-box-wrong','2','3']
    if mode=='wrong-target-partition':
        return ['partition-target-wrong',[['le',['var',str(depth-1)],['constant','0']]],tile]
    if mode.startswith('partition'):
        count=2 if mode=='partition-two-tile' else 1
        cuts=[['le',['var',str(depth-1-axis)],['constant',str(axis)]]
              for axis in range(count)]
        return ['partition-target' if count==2 else 'partition',cuts,tile]
    axes=[[str(int(low)+(1 if axis==0 else 0)),
           str(int(high)+(1 if axis==0 else 0))]
          for axis,(low,high) in enumerate(fields['axes'])]
    if mode=='missing-box':
        axes=[list(pair) for pair in fields['axes']]
        axes[0][1]=str(int(axes[0][0])+1)
        return [*tile,axes]
    middle=syntax.shift_root(source,1)
    steps=[] if mode=='wrong-first' else [['shift','0','-1']]
    return ['chain',['map-index',steps,middle],[*tile,axes]]

def generate(directory,output,mode):
    choices=[]
    for path in sorted(Path(directory).glob('*.sexp')):
        request=syntax.parse(path.read_text())
        fields={field[0]:field[1] for field in request[1:]}
        if len(fields['axes'])<2:continue
        candidate=proposal(fields,mode)
        if candidate is not None:choices.append(['request',path.stem,candidate])
    assert choices,'no multi-axis affine requests'
    output.write_text(syntax.render(['choices',*choices])+'\n')
    return len(choices)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('requests',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--mode',choices=MODES,required=True);args=parser.parse_args()
    print('proposed',generate(args.requests,args.output,args.mode),'untrusted compositions')

if __name__=='__main__':main()
