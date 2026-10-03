"""Compare guarded two-, three- and four-axis pointer programs with a word model."""
from pathlib import Path
import argparse
import hashlib
import json
import native_memory_affine_alias as common
from native_memory_recursive import loop_template
ROOT=common.ROOT
SOURCE=ROOT/'examples/native_memory_axis_alias.c'
WORK=ROOT/'build/native-memory-axis-alias'
NAMES=['axis_copy2','axis_negative2','axis_chain2','axis_copy3','axis_copy4']
DIMENSIONS=[2,2,2,3,4]
PREVIOUS_MAX_CAPS=[4,4,3,3,2]
SIZE=6000

def full_inputs():
    two=[[0,0],[0,9],[9,0],[1,1],[2,2],[4,4],[5,5],[9,9],[16,16],[17,17],[33,1],[61,1]]
    three=[[0,2,2],[1,0,2],[2,2,0],[1,1,1],[2,2,2],[4,4,4],[5,2,2],[9,1,2],[15,1,1],[16,1,1]]
    four=[[0,2,2,2],[1,0,2,2],[2,2,0,2],[2,2,2,0],[1,1,1,1],[2,2,2,2],
          [3,1,1,2],[4,2,2,2],[5,1,1,1],[7,1,1,1],[8,1,1,1]]
    result=[[w,kind,0]+counts+[1]*(4-len(counts))+[-7,11]
        for w,counts_set in enumerate([two,two,two,three,four]) for kind in range(5) for counts in counts_set]
    for w in range(5):
        result += [[w,0,1,3,2,2,2,-2147483648,2147483647],[w,0,0,3,2,2,2,-2147483648,2147483647],
                   [w,5,0,0,2,2,2,3,-7],[w,5,0,-2147483648,2,2,2,3,-7]]
    return result

def source_points(args):
    which,_,start,*_=args
    counts=args[3:3+DIMENSIONS[which]]
    counters=[start,77,91,103];points=[]
    def walk(axis):
        if axis:counters[axis]=0
        while counters[axis]<counts[axis]:
            if axis+1==len(counts):points.append(tuple(counters[:len(counts)]))
            else:walk(axis+1)
            counters[axis]+=1
    walk(0)
    return points,counters

def physical(kind):
    return (1,0) if kind in [0,5] else (0,{1:1,2:1500,3:0,4:16}[kind])

def indices(which,point):
    if which<3:
        index=16*point[0]+point[1]
        return (1023-index,1022-index) if which==1 else (index,index+int(which==0))
    coefficients=[64,8,1] if which==3 else [128,32,4,1]
    index=sum(a*b for a,b in zip(coefficients,point))
    return index,index

def separated(args):
    which,kind=args[:2];block,base=physical(kind)
    cells={'p':set(),'q':set()}
    for point in source_points(args)[0]:
        write,read=indices(which,point);cells['p'].add(write);cells['q'].add(read+base)
        if which==2:cells['q'].add(write+1+base)
    return block!=0 or not cells['p']&cells['q']

def output_model(args,interchange=False,fission=False):
    which,kind,_,_,_,_,_,alpha,beta=args
    a,b=[3*i+1 for i in range(SIZE)],[5*i+7 for i in range(SIZE)]
    block,base=physical(kind);q=[a,b][block]
    points,counters=source_points(args)
    operations=[(point,site) for point in points for site in range(2 if which==2 else 1)]
    if interchange:operations.sort(key=lambda item:(item[0][1],item[0][0],*item[0][2:],item[1]))
    if fission:operations.sort(key=lambda item:(item[1],*item[0]))
    for point,site in operations:
        write,read=indices(which,point)
        assert 0<=write<SIZE and 0<=base+read<SIZE,args
        if site==0:a[write]=common.word(q[base+read]*alpha+point[0]*beta+sum(point[1:]))
        else:
            assert 0<=base+write+1<SIZE,args
            q[base+write+1]=common.word(a[write]+q[base+write+1]*beta+point[0]-point[1])
    return ' '.join(map(str,args+counters+[value for row in zip(a,b) for value in row]))+'\n'

def templates():
    result={}
    for dimensions in [2,3,4]:
        result[f'direct-identity-{dimensions}']=loop_template(dimensions)
        result[f'direct-interchange-{dimensions}']=loop_template(dimensions,[1,0]+list(range(2,dimensions)))
    result.update({
        'schedule-identity-2':'(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2':'(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2':'(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3':'(tile 2 3)','tile-17-13':'(tile 17 13)',
        'invalid-coordinate':'(schedule ((coordinate 8) ordinal) ())'})
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true')
    parser.add_argument('--previous-compiler',type=Path);parser.add_argument('--cases');args=parser.parse_args()
    reference=common.checked_reference(SOURCE,WORK,''.join(output_model(a) for a in full_inputs()))
    if args.reference_only:print('GCC and independent word model agree:',len(full_inputs()),'calls');return
    options=[(name,syntax,{}) for name,syntax in templates().items()]
    options += [(name,templates()['schedule-interchange-2'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    if args.previous_compiler:
        compiler=args.previous_compiler.resolve();stamp=json.loads((compiler.parent/'.guard-build.json').read_text())
        assert hashlib.sha256(compiler.read_bytes()).hexdigest()==stamp['compiler_sha256']
        for name in ['compcert.ini','runtime']:
            link=compiler.parent/name
            if not link.exists():link.symlink_to(common.COMPILER.parent/name,target_is_directory=name=='runtime')
        common.COMPILER=compiler
    else:
        stamp=common.check_build()
        proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
        assert proof['multi_axis_loop_alias_guard_proved'] and proof['multi_axis_loop_alias_guard_csem_asm_route_proved']
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options}
    assert selected<={name for name,_,_ in options}
    configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        dump,cb,ab=common.compile_run(SOURCE,WORK/('before' if args.previous_compiler else 'after')/name,syntax,extra,reference)
        observed=common.observed_functions(dump,NAMES)
        if extra or name=='invalid-coordinate':assert not observed,(name,observed)
        elif not args.previous_compiler:
            expected=set(NAMES) if name.startswith('tile') else {fn for fn,d in zip(NAMES,DIMENSIONS) if d==int(name[-1])}
            assert expected<=set(observed),(name,observed)
            for fn in expected:
                if fn=='axis_chain2' and 'fission' in name:continue
                assert observed[fn]['count_guard_cap']>PREVIOUS_MAX_CAPS[NAMES.index(fn)],(name,fn,observed[fn])
        configurations[name]={'guarded_functions':observed,'actual_calls':len(full_inputs()),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,{fn:v['count_guard_cap'] for fn,v in observed.items()},flush=True)
    report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(args.cases),'previous_compiler':bool(args.previous_compiler),
        'scope':'complete CompCert assembly execution; independent word model, whole pointer buffers, exact public nested-loop exits, two to four axes, signed addresses and alias-sensitive dependences; branches checked separately'}
    (WORK/('before-report.json' if args.previous_compiler else 'smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
