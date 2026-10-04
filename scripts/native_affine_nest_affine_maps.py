"""Run skew and reflection proposals through the existing verified checker."""
from pathlib import Path
import json
import affine_coordinate_candidate as producer
import native_affine_nest_external as external
import native_affine_nest_multiple_pointers as fixture
ROOT=fixture.ROOT;WORK=ROOT/'build/native-affine-nest-affine-maps'

def main():
    fixture.generate();WORK.mkdir(parents=True,exist_ok=True);external.WORK=WORK
    stamp=fixture.unified.check_build();requests=external.export_requests()
    expected=''.join(fixture.output_model(row) for row in fixture.full_inputs())
    witness=(2,0,0,3,2,2,-7)
    reversed_points=sorted(fixture.source_points(witness)[0],key=lambda point:(-point[0],*point[1:]))
    assert fixture.output_model(witness)!=fixture.output_model(witness,point_order=reversed_points)
    fixture.unified.rectangular.common.checked_reference(fixture.SOURCE,WORK,expected)
    configurations={}
    for name,mode,factor in [('skew-plus','skew',1),('skew-minus','skew',-2),
            ('reflect','reflect',1),('wrong-skew','skew-wrong',1),('wrong-reflect','reflect-wrong',1),
            ('resource-limit','skew',1)]:
        candidate=WORK/(name+'.sexp');count=producer.generate(requests,candidate,mode,factor)
        extra={'GUARDCERT_AFFINE_CANDIDATE':str(candidate)}
        if name=='resource-limit':extra['GUARDCERT_FM_ROWS']='0'
        row=fixture.compile_run(name,'external',extra,expected,directory=WORK)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted=set(fixture.NAMES) if name.startswith('skew-') else set(fixture.NAMES)-{'multi_chain2'} if name=='reflect' else set()
        assert guarded==wanted,(name,guarded,wanted)
        configurations[name]=row|{'candidate_sha256':fixture.sha(candidate),'request_count':count}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':fixture.sha(fixture.SOURCE),
        'configurations':configurations,'unsafe_reflection_source_model_witness':list(witness),
        'scope':'actual assembly; external skew and reflection; all arrays and public controls'},indent=2)+'\n')

if __name__=='__main__':main()
