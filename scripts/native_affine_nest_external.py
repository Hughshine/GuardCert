"""Validate externally generated affine candidates in actual complete programs."""
from pathlib import Path
import json,os,subprocess
import external_affine_candidate as producer
import native_affine_nest_multiple_pointers as fixture
from native_zero_trip import function_body
ROOT=fixture.ROOT
WORK=ROOT/'build/native-affine-nest-external'


def export_requests():
    requests=WORK/'requests-full';requests.mkdir(parents=True,exist_ok=True)
    env={k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env|={'GUARDCERT_AFFINE_MODE':'disabled','GUARDCERT_AFFINE_PROFILE':'inferred',
          'GUARDCERT_AFFINE_REQUEST_DIR':str(requests)}
    compiler=fixture.COMPILER
    with (WORK/'export-full.log').open('w') as log:
        result=subprocess.run([str(compiler),'-conf',str(compiler.parent/'compcert.ini'),
            '-stdlib',str(compiler.parent/'runtime'),'-S','-o',str(WORK/'source-full.s'),str(fixture.SOURCE)],
            cwd=WORK,env=env,stdout=log,stderr=subprocess.STDOUT,timeout=600)
    assert result.returncode==0,(WORK/'export-full.log').read_text()[-4000:]
    return requests


def main():
    fixture.generate();WORK.mkdir(parents=True,exist_ok=True)
    stamp=fixture.unified.check_build();requests=export_requests()
    expected=''.join(fixture.output_model(row) for row in fixture.full_inputs())
    fixture.unified.rectangular.common.checked_reference(fixture.SOURCE,WORK,expected)
    configurations={}
    for name,mode,delta in [('identity','identity',1),('shift-plus-1','shift-root',1),
            ('shift-minus-3','shift-root',-3),('wrong-map','wrong-map',1),('drop-point','drop-point',1),
            ('malformed','malformed',1),('resource-limit','shift-root',1)]:
        candidate=WORK/(name+'.sexp')
        if mode=='malformed':candidate.write_text('(unclosed\n');count=0
        else:count=producer.generate(requests,candidate,mode,delta)
        extra={'GUARDCERT_AFFINE_CANDIDATE':str(candidate)}
        if name=='resource-limit':extra['GUARDCERT_FM_ROWS']='0'
        row=fixture.compile_run(name,'external',extra,expected,directory=WORK)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        assert guarded==(set(fixture.NAMES) if name in ['identity','shift-plus-1','shift-minus-3'] else set()),(name,guarded)
        row|={'candidate_sha256':fixture.sha(candidate),'request_count':count}
        configurations[name]=row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':fixture.sha(fixture.SOURCE),'configurations':configurations,
        'scope':'actual assembly for external Loop candidates; complete arrays and all public controls'},indent=2)+'\n')

if __name__=='__main__':main()
