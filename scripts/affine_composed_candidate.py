"""Produce untrusted compositions; every stage requires kernel acceptance."""
from pathlib import Path
import argparse
import external_affine_candidate as syntax

MODES=['tile','partition-tile','partition-two-tile','shift-tile',
       'wrong-first','wrong-witness','wrong-target-partition','missing-box','resource-limit']

def proposal(fields,mode):
    source=fields['source'];depth=len(fields['axes'])
    tile=['tile-box','2','3']
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
        choices.append(['request',path.stem,proposal(fields,mode)])
    assert choices,'no multi-axis affine requests'
    output.write_text(syntax.render(['choices',*choices])+'\n')
    return len(choices)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('requests',type=Path);parser.add_argument('output',type=Path)
    parser.add_argument('--mode',choices=MODES,required=True);args=parser.parse_args()
    print('proposed',generate(args.requests,args.output,args.mode),'untrusted compositions')

if __name__=='__main__':main()
