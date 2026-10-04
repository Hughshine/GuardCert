"""Execute signed source windows and compare every array cell and public exit."""
from pathlib import Path
import argparse,hashlib,itertools,json,re
from native_memory_pointer import loop_template
import native_memory_affine_alias as common
from native_zero_trip import function_body
ROOT=common.ROOT
SOURCE=ROOT/'examples/native_memory_signed_windows.c'
WORK=ROOT/'build/native-memory-signed-windows'
SIZE=4096
CENTER=2048
NAMES=['window_fill1','window_update1','window_neighbor1','window_fill2','window_chain2','window_offset2','window_update3','window_undefined2']
DIMENSIONS=[1,1,1,2,2,2,3,2]
word=common.word

def points(args):
    which,kind,start,n,m,s,u,alpha,beta=args
    return itertools.product(range(start,n),*([range(max(0,m))] if DIMENSIONS[which]>=2 else []),*([range(max(0,s))] if DIMENSIONS[which]>=3 else []))

def output_model(args):
    which,kind,start,n,m,s,u,alpha,beta=args
    array=[3*x+1 for x in range(SIZE)]
    def get(index):
        assert kind==0 and 0<=CENTER+index<SIZE,(args,index)
        return array[CENTER+index]
    def put(index,value):
        assert kind==0 and 0<=CENTER+index<SIZE,(args,index)
        array[CENTER+index]=word(value)
    for coordinate in points(args):
        i=coordinate[0];j=coordinate[1] if len(coordinate)>1 else 0;k=coordinate[2] if len(coordinate)>2 else 0
        linear=i+u;index=16*i+j+u
        if which==0:put(linear,alpha*i+beta)
        elif which==1:put(linear,get(linear)*alpha+beta)
        elif which==2:put(linear,get(linear-1)+alpha)
        elif which==3:put(index,alpha*i+beta*j)
        elif which==4:
            put(index,get(index)*alpha+beta)
            put(index+1,get(index)+get(index+1)*beta+i-j)
        elif which==5:put(16*i+j-1,alpha+i-j)
        elif which==6:
            target=16*i+4*j+k+u;put(target,get(target)*alpha+beta*i+j+k)
        else:put(index,get(index)*alpha+i*beta+j)
    final_i=max(start,n)
    final_j=max(0,m) if DIMENSIONS[which]>=2 and start<n else 77
    final_k=max(0,s) if DIMENSIONS[which]>=3 and start<n and m>0 else 91
    return ' '.join(map(str,list(args)+[final_i,final_j,final_k]+array))+'\n'

def full_inputs():
    result=[]
    shapes=[(-2,3,2,2),(-1,1,1,1),(0,3,2,2),(1,3,2,2),(2,3,1,1),(-3,-1,2,2),(-1,0,1,1),
            (-16,1,1,1),(-65,-64,1,1),(0,64,2,2)]
    for which in range(len(NAMES)):
        for start,n,m,s in shapes:
            for u in [-64,-16,-3,-1,0,1,64]:
                args=(which,0,start,n,m,s,u,-7,11)
                output_model(args);result.append(args)
        for start,n,m,s in [(-2,3,2,2),(1,3,1,1)]:
            result.append((which,0,start,n,m,s,-1,-2147483648,2147483647))
        for start,n in [(2,2),(3,2),(-2147483648,-2147483648),(2147483647,2147483647)]:
            result.append((which,1,start,n,2,2,-2147483648,2147483647,-2147483648))
        if DIMENSIONS[which]>=2:result.append((which,1,-1,3,0,2,-2147483648,2147483647,-2147483648))
        if DIMENSIONS[which]>=3:result.append((which,1,-1,3,2,0,-2147483648,2147483647,-2147483648))
    return list(dict.fromkeys(result))

def literal(value):return '(-2147483647-1)' if value==-2147483648 else str(value)

def reverse_neighbor_witness():
    # Reversing this real dependence changes a complete buffer even though
    # different logical cells of the single pointer are separated.
    args=(2,0,-2,3,1,1,-1,-7,11)
    array=[3*x+1 for x in range(SIZE)]
    for i in reversed(range(args[2],args[3])):
        target=CENTER+i+args[6]
        array[target]=word(array[target-1]+args[7])
    reversed_output=' '.join(map(str,list(args)+[args[3],77,91]+array))+'\n'
    assert reversed_output!=output_model(args)
    return list(args)

def observed_functions(dump):
    found={}
    for fn in NAMES:
        body=function_body(dump,fn)
        if 'switch (0)' not in body:continue
        begin=body.index('switch (0)');end=body.index('continue;',begin);guard=body[begin:end]
        active=re.search(r'\bif\s*\(\$(\w+)\s*<\s*\$(\w+)\)',guard)
        assert active,(fn,guard)
        root,bound=active.groups()
        counts=re.findall(r'\bif\s*\(0\s*<\s*\$(\w+)\)',guard)
        lowers=dict((key,int(value)) for value,key in re.findall(r'\bif\s*\(\s*(-?\d+)\s*<=\s*\$(\w+)\)',guard))
        assert counts and counts[0]==bound and root in lowers,(fn,guard)
        upper={}
        for key in counts+list(lowers):
            caps=re.findall(r'\bif\s*\(\s*(?:!\s*\(\s*)?\$'+key+r'\s*<=\s*(-?\d+)\s*\)',guard)
            assert caps and len(set(caps))==1,(fn,key,caps)
            upper[key]=int(caps[0])
        found[fn]={'count_identifiers':counts,'count_caps':[upper[key] for key in counts],
            'root_iterator':root,'root_lower':lowers[root],'root_upper':upper[root]+1,
            'address_parameter_bounds':{key:[lower,upper[key]+1] for key,lower in lowers.items() if key!=root},
            'whole_source_region':len(counts)==DIMENSIONS[NAMES.index(fn)],'body_bytes':len(body.encode())}
    return found

def templates():
    result={f'direct-identity-{d}':loop_template(d) for d in [1,2,3]}
    result.update({f'direct-interchange-{d}':loop_template(d,[1,0]+list(range(2,d))) for d in [2,3]})
    result.update({'schedule-identity-2':'(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2':'(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2':'(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'schedule-reverse-1':'(schedule ((negative-coordinate 0) ordinal) ((reflect 0)))',
        'invalid-coordinate':'(schedule ((coordinate 8) ordinal) ())',
        'unsupported-tile':'(tile 2 3)'})
    return result

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true');parser.add_argument('--cases');args=parser.parse_args()
    inputs=full_inputs();witness=reverse_neighbor_witness()
    reference=common.checked_reference(SOURCE,WORK,''.join(output_model(row) for row in inputs))
    if args.reference_only:print('Signed source fixture:',len(inputs),'complete GCC outputs agree with the word model');return
    stamp=common.check_build();proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['memory_signed_window_csem_asm_proved']
    proposals=templates();options=[(name,syntax,{}) for name,syntax in proposals.items()]
    options += [(name,proposals['schedule-interchange-2'],extra) for name,extra in
        [('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options}
    assert selected<={name for name,_,_ in options};configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        dump,clight_bytes,assembly_bytes=common.compile_run(SOURCE,WORK/name,'(interval (per-axis '+syntax+'))',extra,reference)
        found=observed_functions(dump)
        if extra or name in ['invalid-coordinate','unsupported-tile']:assert not found,(name,found)
        else:
            if name=='schedule-reverse-1':
                expected=set(NAMES[:2])
                assert 'window_neighbor1' not in found,(name,found)
            else:
                dimensions=2 if name.startswith('schedule') else int(name[-1])
                expected={fn for fn,d in zip(NAMES,DIMENSIONS) if d==dimensions}
            assert expected<=set(found),(name,expected,found)
            assert all(found[fn]['whole_source_region'] for fn in expected),(name,found)
        configurations[name]={'guarded_functions':found,'actual_calls':len(inputs),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':clight_bytes,'assembly_bytes':assembly_bytes}
        print(name,{fn:region['count_caps'] for fn,region in found.items()},flush=True)
    report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'configurations':configurations,
        'full_configuration_suite':not bool(args.cases),
        'dependence_witness':{'input':witness,'separated_cells_do_not_allow_neighbor_reversal':True},
        'scope':'complete CompCert assembly outputs for signed source roots, signed stable address parameters and signed logical indices; all array cells and public exits; accepted direct and scheduled candidates, genuine dependencies and fault or unsupported proposal fallback'}
    (WORK/('smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':main()
