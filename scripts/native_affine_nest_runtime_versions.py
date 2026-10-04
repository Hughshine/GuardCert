"""Execute checked runtime range versions for the same external fission candidate."""
import json,os,subprocess
from pathlib import Path
import external_affine_candidate as producer
import native_affine_nest_fission as fixture
from native_zero_trip import function_body
ROOT=fixture.ROOT;WORK=ROOT/'build/native-affine-nest-runtime-versions'
COMPILER=ROOT/'build/compcert-guardcert-versions/ccomp'


def check_build():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']=='AffineNestRuntimeVersions.compile_guardcert_versions'
    assert stamp['compiler_sha256']==fixture.memory.sha(COMPILER)
    for path,digest in (stamp['proof_sources']|stamp['native_sources']).items():assert fixture.memory.sha(ROOT/path)==digest,path
    proof_path=ROOT/'build/affine-nest-foundation-prototype-report.json'
    assert stamp['prototype_proof_report_sha256']==fixture.memory.sha(proof_path)
    assert json.loads(proof_path.read_text())['versions_whole_program_assumptions_match_baseline']
    return stamp


def inputs():
    return fixture.full_inputs()+[(which,mode,0,1,m,p,alpha) for which in range(4) for mode in range(5)
        for m,p in [(2,2),(10,2),(12,2),(13,2),(16,2),(40,2)] for alpha in [-7,2**31-1]]


def generate():
    text=fixture.SOURCE.read_text().split('int main(void)',1)[0]+'int main(void){\n'
    text+=''.join('multi_case('+','.join(map(fixture.literal,row))+');\n' for row in inputs())
    source=WORK/'runtime-versions.c';source.write_text(text+'return 0;}\n');return source


def compile_run(name,source,expected,extra):
    work=WORK/name;work.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_PROFILE':'inferred','GUARDCERT_AFFINE_DIAGNOSTICS':'1'}|extra
    with (work/'compile.log').open('w') as log:
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),'-stdlib',str(COMPILER.parent/'runtime'),
            '-dclight','-S','-o',str(work/'program.s'),str(source)],cwd=work,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    assert result.returncode==0,(work/'compile.log').read_text()[-4000:]
    subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
    with (work/'output.txt').open('w') as output:subprocess.run([str(work/'program')],stdout=output,text=True,check=True,timeout=180)
    assert (work/'output.txt').read_text()==expected,name
    dump_path=work/(source.stem+'.light.c');dump=dump_path.read_text()
    functions={fn:{'guarded':function_body(dump,fn).count('for (')>depth,'emitted_loops':function_body(dump,fn).count('for (')}
               for fn,depth in zip(fixture.NAMES,fixture.DEPTHS)}
    return {'actual_calls':len(inputs()),'functions':functions,'assembly_sha256':fixture.memory.sha(work/'program.s'),
        'clight_sha256':fixture.memory.sha(dump_path),'output_sha256':fixture.memory.sha(work/'output.txt'),
        'compile_log_sha256':fixture.memory.sha(work/'compile.log'),'all_arrays_and_public_controls_match_source_model':True}


def main():
    WORK.mkdir(parents=True,exist_ok=True);stamp=check_build();source=generate()
    counterexamples=[(2,0,0,3,2,2,-7),(2,0,0,1,40,2,-7),(1,0,0,1,2,2,-7),(2,0,0,1,16,2,-7)]
    for args,order in zip(counterexamples,['fission','fission','reverse-fission','fission']):
        assert fixture.output_model(args)!=fixture.output_model(args,order),args
    narrow_witnesses=[(0,0,0,1,12,2,-7),(2,0,0,1,12,2,-7)]
    for args in narrow_witnesses:assert fixture.output_model(args)==fixture.output_model(args,'fission')
    expected=''.join(fixture.output_model(row) for row in inputs())
    fixture.memory.unified.rectangular.common.checked_reference(source,WORK,expected)
    requests=WORK/'requests';requests.mkdir(exist_ok=True)
    export=compile_run('export',source,expected,{'GUARDCERT_AFFINE_MODE':'disabled','GUARDCERT_AFFINE_REQUEST_DIR':str(requests)})
    configurations={'export':export}
    for name,mode,extra in [('identity','identity',{}),('single-identity','identity',{'GUARDCERT_AFFINE_CONDITION_SEARCH':'disabled'}),
        ('wide-fission','fission',{'GUARDCERT_AFFINE_CONDITION_SEARCH':'disabled'}),
            ('versioned-fission','fission',{}),('unsafe-extended','fission',{'GUARDCERT_AFFINE_VERSION_BOUND_HIGH':'17'}),('versioned-reverse','reverse-fission',{}),
            ('wrong-map','wrong-map',{}),('resource-limit','fission',{'GUARDCERT_FM_ROWS':'0'})]:
        candidate=WORK/(name+'.sexp');count=producer.generate(requests,candidate,mode,1,source_match=True)
        row=compile_run(name,source,expected,{'GUARDCERT_AFFINE_MODE':'external','GUARDCERT_AFFINE_CANDIDATE':str(candidate)}|extra)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted={'identity':set(fixture.NAMES),'single-identity':set(fixture.NAMES),'wide-fission':set(fixture.NAMES)-{'fission_future2'},
                'versioned-fission':set(fixture.NAMES),'unsafe-extended':set(fixture.NAMES)-{'fission_future2'},'versioned-reverse':set(fixture.NAMES)-{'fission_pointwise2'},
                'wrong-map':set(),'resource-limit':set()}[name]
        assert guarded==wanted,(name,guarded,wanted)
        row|={'candidate_sha256':fixture.memory.sha(candidate),'request_count':count}
        configurations[name]=row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':fixture.memory.sha(source),'configurations':configurations,
        'source_model_counterexamples':counterexamples,'nondead_second_version_witnesses':narrow_witnesses,
        'scope':'actual assembly; runtime chains of checked range profiles for the same externally supplied candidate'},indent=2)+'\n')

if __name__=='__main__':main()
