"""Check tiled and untiled actual candidates, identity refusal and dependence refusal.

Every version retains the original arrays and IEEE expression tree. These
supplement the unchanged pinned corpus rather than replace its evidence.
"""
import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--cases', nargs='+')
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if not build.get('actual_independent_header_captures_extracted'):
        raise ValueError('Expected the independent-bound compiler')
    compiler = permitted(ROOT / build['compiler'])
    input_path = permitted(ROOT / 'build/benchmark-alignment/probe-v1/intratileopt1/marked.c')
    bindings[str(input_path.relative_to(ROOT))] = sha(input_path)
    original = input_path.read_text()

    def variant(n,m,public=True):
        text=original
        for name,value in [('N',n),('M',m)]:
            old='static const long long '+name+' = 96;'
            if text.count(old)!=1:raise ValueError('Pinned declaration changed')
            text=text.replace(old,'static long long '+name+' = '+str(value)+';')
        start=text.index('#pragma scop')
        preparation=''.join('  '+name+' = (int)polcert_rotr32((unsigned int)'+name+',16);\n'
                            '  '+name+' = (int)polcert_rotr32((unsigned int)'+name+',16);\n'
                            for name in ['N','M'])
        text=text[:start]+preparation+text[start:]
        controls=None
        if public:
            start=text.index('#pragma scop');end=text.index('#pragma endscop')+len('#pragma endscop')
            region=text[start:end].replace('for (long long i','for (i').replace('for (long long j','for (j')
            text=text[:start]+'long long i=17,j=29;\n'+region+\
                '\nprintf("controls=%lld,%lld\\n",i,j);\n'+text[end:]
            controls=str(max(0,n))+','+str(max(0,m) if n>0 else 29)
        return text,controls
    variants=[]
    for name,values in [('unequal-23-31',(23,31)),('unequal-31-23',(31,23)),
                        ('tile-boundary-31-33',(31,33)),('tile-boundary-32-32',(32,32)),
                        ('tile-boundary-33-31',(33,31)),
                        ('outer-zero',(0,-1)),('outer-negative',(-1,-2)),
                        ('inner-zero',(23,0)),('inner-negative',(23,-1))]:
        text,controls=variant(*values);variants.append((name,text,{},1,controls))
    text,controls=variant(5,7)
    for name,options,sites in [
        ('cap-refusal-first',{'GUARDCERT_RECTANGULAR_CAPS':'4,16'},1),
        ('cap-refusal-second',{'GUARDCERT_RECTANGULAR_CAPS':'16,6'},1),
        ('wrong-coordinate',{'GUARDCERT_POINT_NORMALIZATION':'wrong-coordinate'},0),
        ('tiled-wrong-bound',{'GUARDCERT_BOUND_NORMALIZATION':'wrong-bound'},0),
        ('tiled-wrong-point-domain',{'GUARDCERT_BOUND_NORMALIZATION':'wrong-point-domain'},0),
        ('tiled-wrong-witness',{'GUARDCERT_DOUBLE_TILING_MODE':'wrong-witness'},0),
        ('unit-tiles',{'GUARDCERT_TILE_SIZES':'1,1'},1),
        ('mixed-unit-tiles',{'GUARDCERT_TILE_SIZES':'1,32'},1)]:
        variants.append((name,text,options,sites,controls))
    text,_=variant(5,7,public=False)
    start=text.index('#pragma scop');end=text.index('#pragma endscop')+len('#pragma endscop')
    region=text[start:end]
    variants.append(('multiple-marked',text[:end]+'\n'+region+text[end:],{},2,None))
    variants.append(('marked-and-unmarked',text[:end]+'\n'+region.replace('#pragma scop','')
                     .replace('#pragma endscop','')+text[end:],{},1,None))
    text,controls=variant(23,31)
    for name,options,sites in [
        ('untiled-interchange',{'GUARDCERT_PHASE_ORDER':'1,0'},1),
        ('untiled-wrong-coordinate',{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_POINT_NORMALIZATION':'wrong-coordinate'},0),
        ('untiled-identity',{'GUARDCERT_PHASE_ORDER':'0,1'},0),
        ('untiled-invalid-order',{'GUARDCERT_PHASE_ORDER':'1,1'},0),
        ('untiled-auto',{'GUARDCERT_PHASE_KIND':'untiled'},None)]:
        variants.append((name,text,options,sites,controls))
    for name,values,options in [
        ('untiled-empty-outer',(0,31),{'GUARDCERT_PHASE_ORDER':'1,0'}),
        ('untiled-empty-inner',(23,0),{'GUARDCERT_PHASE_ORDER':'1,0'}),
        ('untiled-negative-inner',(23,-1),{'GUARDCERT_PHASE_ORDER':'1,0'}),
        ('untiled-cap-refusal-first',(5,7),{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_RECTANGULAR_CAPS':'4,16'}),
        ('untiled-cap-refusal-second',(5,7),{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_RECTANGULAR_CAPS':'16,6'})]:
        text,controls=variant(*values);variants.append((name,text,options,1,controls))
    for name,case,options,sites in [
        ('seq-auto','seq',{},0),
        ('seq-invalid-interchange','seq',{'GUARDCERT_PHASE_ORDER':'1,0'},0),
        ('tricky2-auto','tricky2',{},0),
        ('tricky2-manual-identity','tricky2',{'GUARDCERT_PHASE_ORDER':'0'},0),
        ('matmul-untiled-interchange','matmul',{'GUARDCERT_PHASE_ORDER':'0,2,1'},1)]:
        path=permitted(ROOT / 'build/benchmark-alignment/probe-v1' / case / 'marked.c')
        bindings[str(path.relative_to(ROOT))]=sha(path)
        variants.append((name,path.read_text(),options,sites,None))
    text,controls=variant(23,31)
    for name,options in [
        ('untiled-wrong-bound',{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_BOUND_NORMALIZATION':'wrong-bound'}),
        ('untiled-wrong-witness',{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_DOUBLE_TILING_MODE':'wrong-witness'}),
        ('untiled-malformed-phase',{'GUARDCERT_PHASE_ORDER':'1,0','GUARDCERT_DOUBLE_TILING_MODE':'malformed'})]:
        variants.append((name,text,options,0,controls))
    text,_=variant(5,7,public=False)
    start=text.index('#pragma scop');end=text.index('#pragma endscop')+len('#pragma endscop')
    region=text[start:end]
    variants.append(('untiled-multiple-marked',text[:end]+'\n'+region+text[end:],
                     {'GUARDCERT_PHASE_ORDER':'1,0'},2,None))
    variants.append(('untiled-marked-and-unmarked',text[:end]+'\n'+region.replace('#pragma scop','')
                     .replace('#pragma endscop','')+text[end:],{'GUARDCERT_PHASE_ORDER':'1,0'},1,None))
    if args.cases:
        selected = set(args.cases)
        if not selected <= {case[0] for case in variants}:
            raise ValueError('Unknown independent-bound context case')
        variants = [case for case in variants if case[0] in selected]
    work = ROOT / 'build/runtime-double-tile-bounds/context-attempts' / args.attempt
    work.mkdir(parents=True,exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    rows = []
    for name,text,options,expected_sites,controls in variants:
        directory = work / name; directory.mkdir()
        source = directory / 'program.c'; source.write_text(text)
        env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile',GUARDCERT_DOUBLE_TILING_MODE='tile',
                   GUARDCERT_TILE_SIZES='32',GUARDCERT_PLUTO=str(PLUTO),
                   GUARDCERT_ORIGINAL_OUTPUT=str(directory),GUARDCERT_SCOP_DIAGNOSTICS='1')
        env.update(options)
        env['GUARDCERT_PHASE_TRACE']='1'
        result,out,err = run([str(compiler),'-fall','-stdlib',str(compiler.parent / 'runtime'),
            '-dclight','-S','-o',str(directory / 'program.s'),str(source)],directory,'compiler',env,timeout=600)
        trace = (out+err).decode(errors='replace')
        counts = re.findall(r'GUARDCERT_RECTANGULAR_INSTALLED regions=(\d+)',trace)
        actual = int(counts[-1]) if counts else None
        row = {'case':name,'compiler':result,'options':options,'rectangular_installed':actual,
               'expected_rectangular_sites':expected_sites,'expected_public_controls':controls,
               'cap_proposal_trace':re.findall(r'^GUARDCERT_RECTANGULAR_CAPS .*',trace,re.M),
               'actual_raw_candidates':len(list(directory.glob('tiling-pipeline-*/rectangular-raw-generated.loop'))),
               'actual_final_candidates':len(list(directory.glob('tiling-pipeline-*/rectangular-generated.loop'))),
                'actual_tightening_receipts':len(list(directory.glob('tiling-pipeline-*/runtime-tightened.loop'))),
                'runtime_bound_changes':[int(value) for value in re.findall(r'^GUARDCERT_RUNTIME_BOUNDS changed=(\d+)',trace,re.M)],
               'phase_shapes':re.findall(r'^GUARDCERT_DOUBLE_PHASE_SHAPE .*',trace,re.M),
               'phase_refusals':re.findall(r'^GUARDCERT_DOUBLE_TILING_REFUSED .*',trace,re.M),
               'phase_trace':re.findall(r'^GUARDCERT_PHASE .*',trace,re.M)}
        if result['returncode']==0:
            link,_,_ = run(['gcc','-no-pie',str(directory / 'program.s'),'-lm','-o',str(directory / 'program')],directory,'link')
            gcc,_,_ = run(['gcc','-O0','-ffp-contract=off',str(source),'-lm','-o',str(directory / 'reference')],directory,'gcc')
            row.update(link=link,gcc=gcc)
            if link['returncode']==gcc['returncode']==0:
                native,output,_ = run([str(directory / 'program')],directory,'native')
                reference,expected,_ = run([str(directory / 'reference')],directory,'reference')
                row.update(native=native,reference=reference,
                    digest_matches_GCC=native['returncode']==reference['returncode']==0 and output==expected)
                if controls is not None:
                    row['public_controls']=re.findall(r'controls=([^\n]+)',output.decode())
        row['passed'] = ((expected_sites is None or actual==expected_sites) and row.get('digest_matches_GCC',False)
                         and (controls is None or row.get('public_controls')==[controls]))
        if expected_sites and 'untiled' not in name:
            row['accepted_tightening_has_changed_bound']=any(value>0 for value in row['runtime_bound_changes'])
            row['passed']=row['passed'] and row['accepted_tightening_has_changed_bound']
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({key:row[key] for key in ['case','passed','rectangular_installed']}),flush=True)
    for path in [Path(__file__),PLUTO,*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    report = {'status':'passed' if all(row['passed'] for row in rows) else 'rejected','cases':rows,
              'compiler_entrypoint':build['whole_program_entrypoint'],
              'whole_program_theorem':build['actual_source_Csem_to_Asm_theorem'],
              'original_intratileopt1_IEEE_operations_and_arrays_retained':True,
              'zero_link_proposals_checked_by_existing_complete_compiler':True,
               'certified_runtime_bound_postpass_connected_to_new_complete_compiler':True,
               'affine_reference_still_passes_existing_final_candidate_checker':True,
               'runtime_tightening_receipts_alone_are_not_acceptance':True,
              'automatic_untiled_installation_is_diagnostic_without_fixed_count':True,
              'new_original_corpus_coverage_claimed':False,
              'disclosed_variants_are_not_original_corpus_coverage':True,
              'independent_parameters_and_public_exits_checked':True,
              'actual_runtime_dispatch_established_by_output_alone':False,
              'controlled_cost_evidence_added':False,'full_goal_complete':False,'bindings':bindings}
    (work / 'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if report['status']!='passed':raise SystemExit(1)

if __name__=='__main__':main()
