"""Check composed affine proposals on actual assembly and a separate word model."""
import argparse,json
import affine_composed_candidate as producer
import native_affine_nest_fission as fixture
WORK=fixture.ROOT/'build/native-affine-nest-composition'

def tile_points(args,shift=0):
    return sorted(fixture.source_points(args)[0],
                  key=lambda point:((point[0]+shift)//2,point[1]//3,*point))

def main(start=None):
    fixture.WORK=WORK;fixture.generate();WORK.mkdir(parents=True,exist_ok=True)
    stamp=fixture.memory.unified.check_build();requests=fixture.export_requests()
    expected=''.join(fixture.output_model(row) for row in fixture.full_inputs())
    witness=(2,0,0,3,4,2,-7)
    for shift in [0,1]:
        assert fixture.output_model(witness)!=fixture.output_model(
            witness,point_order=tile_points(witness,shift)),('future dependence',shift)
    missing_witness=(0,0,0,3,2,2,-7)
    missing_points=[point for point in tile_points(missing_witness) if point[0]<=0]
    assert fixture.output_model(missing_witness)!=fixture.output_model(missing_witness,point_order=missing_points)
    fixture.memory.unified.rectangular.common.checked_reference(fixture.SOURCE,WORK,expected)
    configurations={}
    binding={'compiler_sha256':stamp['compiler_sha256'],'source_sha256':fixture.memory.sha(fixture.SOURCE)}
    if start is not None:
        assert json.loads((WORK/'partial-build.json').read_text())==binding
        configurations=json.loads((WORK/'partial-report.json').read_text())
        assert set(configurations)==set(producer.MODES[:producer.MODES.index(start)])
        for name,row in configurations.items():
            for field,filename in [('assembly_sha256','program.s'),('output_sha256','output.txt'),
                                   ('compile_log_sha256','compile.log')]:
                assert fixture.memory.sha(WORK/name/filename)==row[field],(name,field)
            assert (WORK/name/'output.txt').read_text()==expected
    else:
        (WORK/'partial-build.json').write_text(json.dumps(binding,indent=2)+'\n')
    for mode in producer.MODES[producer.MODES.index(start) if start is not None else 0:]:
        candidate=WORK/(mode+'.sexp');count=producer.generate(requests,candidate,mode)
        extra={'GUARDCERT_FM_ROWS':'0'} if mode=='resource-limit' else {}
        row=fixture.compile_run(mode,candidate,expected,extra)
        guarded={fn for fn,facts in row['functions'].items() if facts['guarded']}
        wanted=(set(fixture.NAMES)-{'fission_future2'} if mode in
                ['tile','partition-tile','partition-two-tile','shift-tile'] else set())
        assert guarded==wanted,(mode,guarded,wanted)
        configurations[mode]=row|{'request_count':count}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(mode,sorted(guarded),flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'entrypoint':stamp['proved_entrypoint'],
        'source_sha256':fixture.memory.sha(fixture.SOURCE),'configurations':configurations,
        'unsafe_future_tile_word_model_witness':list(witness),
        'unsafe_target_partial_partition_word_model_witness':list(missing_witness),
        'scope':'actual assembly; complete arrays and public controls; every composition stage checked'},
        indent=2)+'\n')

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--start',choices=producer.MODES)
    main(parser.parse_args().start)
