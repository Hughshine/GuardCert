"""Import complete and incomplete affine domain partitions through the checker."""
import json
import itertools
import native_affine_nest_fission as fixture
import external_affine_candidate as producer

WORK=fixture.ROOT/'build/native-affine-nest-domain-split'


def reordered_points(args,count=1,reverse=False,drop=False,duplicate=False):
    points=fixture.source_points(args)[0]
    signs=list(itertools.product([True,False],repeat=count))
    if reverse:signs.reverse()
    pieces=[[point for point in points if all((point[axis]<=axis)==sign
        for axis,sign in enumerate(bits))] for bits in signs]
    if drop:pieces.pop()
    if duplicate:pieces.append(pieces[-1])
    return [point for piece in pieces for point in piece]


def main():
    fixture.WORK=WORK
    fixture.generate();WORK.mkdir(parents=True,exist_ok=True)
    stamp=fixture.memory.unified.check_build();requests=fixture.export_requests()
    expected=''.join(fixture.output_model(row) for row in fixture.full_inputs())
    witness=(2,0,-2,3,4,2,-7)
    counterexamples={}
    for name,options in [('split-two',{'count':2}),('split-reverse',{'reverse':True}),
                         ('split-drop',{'drop':True}),('split-duplicate',{'duplicate':True})]:
        assert fixture.output_model(witness)!=fixture.output_model(witness,point_order=reordered_points(witness,**options)),name
        counterexamples[name]=list(witness)
    fixture.memory.unified.rectangular.common.checked_reference(fixture.SOURCE,WORK,expected)
    configurations={}
    for name,mode,extra in [('identity','identity',{}),('split-one','split-one',{}),
            ('split-two','split-two',{}),('split-reverse','split-reverse',{}),
            ('split-drop','split-drop',{}),('split-duplicate','split-duplicate',{}),
            ('resource-limit','split-one',{'GUARDCERT_FM_ROWS':'0'})]:
        candidate=WORK/(name+'.sexp');producer.generate(requests,candidate,mode,1)
        row=fixture.compile_run(name,candidate,expected,extra)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted={'identity':set(fixture.NAMES),'split-one':set(fixture.NAMES),
                'split-two':set(fixture.NAMES)-{'fission_future2'},
                'split-reverse':set(fixture.NAMES)-{'fission_future2'},
                'split-drop':set(),'split-duplicate':set(),'resource-limit':set()}[name]
        assert guarded==wanted,(name,guarded,wanted)
        configurations[name]=row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':fixture.memory.sha(fixture.SOURCE),
        'configurations':configurations,'independent_word_model_counterexamples':counterexamples,
        'scope':'actual assembly; checked affine domain partition and schedule'},indent=2)+'\n')

if __name__=='__main__':main()
