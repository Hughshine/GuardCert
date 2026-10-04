"""Check fixed affine address parameters with complete compiler execution."""
from pathlib import Path
import argparse
import hashlib
import itertools
import json
import re
import native_memory_affine_alias as common
from native_memory_pointer import loop_template
from native_zero_trip import function_body

ROOT=common.ROOT
SOURCE=ROOT/'examples/native_memory_address_parameters.c'
WORK=ROOT/'build/native-memory-address-parameters'
NAMES=['param_copy2','param_negative2','param_chain2','param_mixed2','param_copy3','param_linear1','param_undefined2']
DIMENSIONS=[2,2,2,2,3,1,2]
PARAMETER_NAMES=[['u','v'],['u','v'],['u','v'],['u'],['u','v'],['u','v'],['local_u','local_v']]
BOUND_NAMES=['n','m','s']
BUFFER_SIZE=4096


def full_inputs():
    result=[]
    for which,dims in enumerate(DIMENSIONS):
        if dims==1:counts=[[0,1,1],[1,1,1],[2,1,1],[8,1,1],[32,1,1],[465,1,1],[466,1,1]]
        elif dims==2:counts=[[0,2,1],[2,0,1],[1,1,1],[2,3,1],[4,4,1],[17,1,1],[60,1,1],[61,1,1],[64,1,1],[65,17,1]]
        else:counts=[[0,2,2],[2,0,2],[2,2,0],[1,1,1],[2,2,2],[4,3,2],[14,1,1],[15,1,1],[17,9,9]]
        for kind in range(5):
            for n,m,s in counts:result.append([which,kind,0,n,m,s,3,7,-7,11])
        for u,v in [(0,0),(1,0),(0,1),(63,63),(64,1),(1,64),(65,65),(-1,0),(0,-1),(-17,-17)]:
            for kind in [0,1,3]:result.append([which,kind,0,3,2,2,u,v,-7,11])
        result += [[which,0,1,3,2,2,3,7,-2147483648,2147483647],
                   [which,0,0,3,2,2,3,7,-2147483648,2147483647],
                   [which,5,0,0,2,2,-2147483648,2147483647,-2147483648,2147483647],
                   [which,5,0,-2147483648,2,2,-2147483648,2147483647,-7,11]]
    return result


def word(value):return (value+2**31)%2**32-2**31


def locations(kind):
    return ('a',256),('b',256) if kind==0 else ('a',{1:257,2:2000,3:256,4:272}[kind])


def source_points(which,start,n,m,s):
    return itertools.product(range(start,n),*([range(m)] if DIMENSIONS[which]>=2 else []),*([range(s)] if DIMENSIONS[which]>=3 else []))


def accesses(which,coordinates,u,v):
    i=coordinates[0];j=coordinates[1] if len(coordinates)>=2 else 0;k=coordinates[2] if len(coordinates)>=3 else 0
    if which==1:return [('p',1023-16*i-j-u),('q',1022-16*i-j-v)]
    if which==4:return [('p',64*i+8*j+k+u+16),('q',64*i+8*j+k+v+16)]
    if which==5:return [('p',2*i+u+32),('q',2*i+v+33)]
    if which==3:return [('p',16*i+j+u+32),('q',16*i+j+u+33)]
    if which==2:return [('p',16*i+j+u+32),('q',16*i+j+v+32),('q',16*i+j+v+33)]
    return [('p',16*i+j+u+32),('q',16*i+j+v+33)]


def output_model(args,fission=False,interchange=False):
    which,kind,start,n,m,s,u,v,alpha,beta=args
    buffers={'a':[3*x+1 for x in range(BUFFER_SIZE)],'b':[5*x+7 for x in range(BUFFER_SIZE)]}
    bases={} if kind==5 else dict(zip(['p','q'],locations(kind)))
    def read(pointer,index):
        name,base=bases[pointer];position=base+index
        assert 0<=position<BUFFER_SIZE,(args,pointer,index,base)
        return buffers[name][position]
    def write(pointer,index,value):
        name,base=bases[pointer];position=base+index
        assert 0<=position<BUFFER_SIZE,(args,pointer,index,base)
        buffers[name][position]=word(value)
    operations=[(coordinates,site) for coordinates in source_points(which,start,n,m,s) for site in range(2 if which==2 else 1)]
    if fission:operations.sort(key=lambda item:(item[1],item[0]))
    if interchange:operations.sort(key=lambda item:(item[0][1],item[0][0],*item[0][2:],item[1]))
    for coordinates,site in operations:
        i=coordinates[0];j=coordinates[1] if len(coordinates)>=2 else 0;k=coordinates[2] if len(coordinates)>=3 else 0
        access=accesses(which,coordinates,u,v)
        if site==1:write(*access[2],read(*access[0])+read(*access[2])*beta+i-j+u-v)
        elif which==3:write(*access[0],read(*access[1])*alpha+u*beta+i+j)
        else:write(*access[0],read(*access[1])*alpha+i*beta+j+k)
    exits=[max(start,n),77,91]
    if start<n and DIMENSIONS[which]>=2:exits[1]=max(0,m)
    if start<n and m>0 and DIMENSIONS[which]>=3:exits[2]=max(0,s)
    values=args+exits+[value for pair in zip(buffers['a'],buffers['b']) for value in pair]
    return ' '.join(map(str,values))+'\n'


def separated(args):
    which,kind,start,n,m,s,u,v,alpha,beta=args
    if kind==5:return False
    bases=dict(zip(['p','q'],locations(kind)));cells={'p':set(),'q':set()}
    for coordinates in source_points(which,start,n,m,s):
        for pointer,index in accesses(which,coordinates,u,v):
            block,base=bases[pointer];cells[pointer].add((block,base+index))
    return not (cells['p']&cells['q'])


def observed_functions(dump):
    found={}
    for which,fn in enumerate(NAMES):
        body=function_body(dump,fn)
        if 'switch (0)' not in body:continue
        begin=body.index('switch (0)');end=body.index('continue;',begin);guard=body[begin:end]
        count_identifiers=re.findall(r'\bif\s*\(0\s*<\s*\$(\w+)\)',guard)
        parameter_identifiers=re.findall(r'\bif\s*\(0\s*<=\s*\$(\w+)\)',guard)
        root=re.search(r'\bif\s*\(\$(\w+)\s*==\s*0U?\)',guard)
        assert count_identifiers and parameter_identifiers and root,(fn,guard)
        assert count_identifiers==BOUND_NAMES[DIMENSIONS[which]-len(count_identifiers):DIMENSIONS[which]],(fn,count_identifiers)
        limits={}
        for identifier in count_identifiers+parameter_identifiers:
            matches=re.findall(r'\$'+identifier+r'\s*<=\s*(\d+)',guard)
            assert matches and len(set(matches))==1,(fn,identifier,matches)
            limits[identifier]=int(matches[0])
        found[fn]={'count_guard_caps':[limits[x] for x in count_identifiers],
            'count_identifiers':count_identifiers,'root_iterator':root[1],
            'address_parameter_identifiers':parameter_identifiers,
            'address_parameter_caps':[limits[x]+1 for x in parameter_identifiers],
            'whole_source_region':len(count_identifiers)==DIMENSIONS[which],'body_bytes':len(body.encode())}
    return found


def templates():
    result={f'direct-identity-{d}':loop_template(d) for d in [1,2,3]}
    result.update({f'direct-interchange-{d}':loop_template(d,[1,0]+list(range(2,d))) for d in [2,3]})
    result.update({'schedule-identity-2':'(schedule ((coordinate 0) (coordinate 1) ordinal) ())',
        'schedule-interchange-2':'(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))',
        'schedule-fission-2':'(schedule (ordinal (coordinate 0) (coordinate 1)) ())',
        'tile-2-3':'(tile 2 3)','tile-17-13':'(tile 17 13)',
        'invalid-coordinate':'(schedule ((coordinate 8) ordinal) ())'})
    return result


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--reference-only',action='store_true');parser.add_argument('--cases')
    parser.add_argument('--previous-compiler',type=Path)
    args=parser.parse_args();inputs=full_inputs()
    reference=common.checked_reference(SOURCE,WORK,''.join(output_model(a) for a in inputs))
    if args.reference_only:print('address parameters fixture:',len(inputs),'GCC calls match the word model');return
    if args.previous_compiler:
        common.COMPILER=args.previous_compiler.resolve()
        stamp=json.loads((common.COMPILER.parent/'.guard-build.json').read_text())
        assert hashlib.sha256(common.COMPILER.read_bytes()).hexdigest()==stamp['compiler_sha256']
    else:
        stamp=common.check_build();proof=json.loads((ROOT/'build/guard-memory-proof-report.json').read_text())
        assert proof['pointer_affine_address_parameters_csem_asm_proved']
    options=[(name,syntax,{}) for name,syntax in templates().items()]
    options += [(name,templates()['schedule-interchange-2'],extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    selected=set(args.cases.split(',')) if args.cases else {name for name,_,_ in options};assert selected<={name for name,_,_ in options}
    configurations={}
    for name,syntax,extra in options:
        if name not in selected:continue
        dump,cb,ab=common.compile_run(SOURCE,WORK/('before' if args.previous_compiler else 'after')/name,'(per-axis '+syntax+')',extra,reference)
        found=observed_functions(dump)
        if args.previous_compiler or extra or name=='invalid-coordinate':assert not found,(name,found)
        else:
            expected={fn for fn,d in zip(NAMES,DIMENSIONS) if d>=2} if name.startswith('tile') else {fn for fn,d in zip(NAMES,DIMENSIONS) if d==int(name[-1])}
            assert expected<=set(found),(name,found)
            assert all(found[fn]['whole_source_region'] for fn in expected),(name,found)
        configurations[name]={'guarded_functions':found,'actual_calls':len(inputs),
            'full_arrays_and_public_counters_match_model_and_gcc':True,'clight_bytes':cb,'assembly_bytes':ab}
        print(name,found,flush=True)
    report={'status':'passed','compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'full_configuration_suite':not bool(args.cases),'previous_compiler':bool(args.previous_compiler),
        'scope':'complete CompCert assembly execution; affine address temporaries, separate signed RHS scalars, real pointer aliasing, source fallback outside address ranges, empty-loop null and undefined operands, complete buffers and public exits'}
    (WORK/('before-report.json' if args.previous_compiler else 'smoke-report.json' if args.cases else 'report.json')).write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
