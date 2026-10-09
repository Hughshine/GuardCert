"""Run independent M/N/K versions of original matmul and complete public contexts.

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
    input_path = permitted(ROOT / 'build/benchmark-alignment/probe-v1/matmul/marked.c')
    bindings[str(input_path.relative_to(ROOT))] = sha(input_path)
    original = input_path.read_text()

    def variant(m, n, k, public=False):
        text = original
        for name, value in [('M',m),('N',n),('K',k)]:
            old = 'static const long long '+name+' = 96;'
            if text.count(old) != 1:
                raise ValueError('Original independent declaration changed: '+name)
            text = text.replace(old, 'static long long '+name+' = '+str(value)+';')
        start = text.index('#pragma scop')
        # These runtime calls preserve the chosen values while preventing the
        # conditions from being solely a constant-input dispatch experiment.
        preparation = ''.join('  '+name+' = (int)polcert_rotr32((unsigned int)'+name+',16);\n'
                              '  '+name+' = (int)polcert_rotr32((unsigned int)'+name+',16);\n'
                              for name in ['M','N','K'])
        text = text[:start]+preparation+text[start:]
        expected = None
        if public:
            start = text.index('#pragma scop')
            end = text.index('#pragma endscop')+len('#pragma endscop')
            region = text[start:end]
            for name in ['i','j','k']:
                region = region.replace('for (long long '+name, 'for ('+name)
            text = text[:start]+'long long i=17,j=29,k=41;\n'+region+\
                '\nprintf("controls=%lld,%lld,%lld\\n",i,j,k);\n'+text[end:]
            expected = ','.join(map(str,[max(0,m),max(0,n) if m>0 else 29,
                                        max(0,k) if m>0 and n>0 else 41]))
        return text, expected

    variants = []
    for name, values in [('unequal-23-31-33',(23,31,33)),('unequal-33-23-31',(33,23,31)),
                         ('asymmetric-98-5-7',(98,5,7)),('outer-zero',(0,-1,-2)),
                         ('outer-negative',(-1,-2,-3)),('inner-zero',(23,0,-1)),
                         ('inner-negative',(23,-1,-2)),('leaf-zero',(23,31,0)),
                         ('leaf-negative',(23,31,-1))]:
        text, controls = variant(*values, public=True)
        variants.append((name,text,{},1,controls))
    text, controls = variant(5,7,9,public=True)
    for name, options, sites in [
        ('cap-refusal-first',{'GUARDCERT_RECTANGULAR_CAPS':'4,16,16'},1),
        ('cap-refusal-second',{'GUARDCERT_RECTANGULAR_CAPS':'16,6,16'},1),
        ('cap-refusal-third',{'GUARDCERT_RECTANGULAR_CAPS':'16,16,8'},1),
        ('cap-static-refusal',{'GUARDCERT_RECTANGULAR_CAPS':'0,16,16'},0),
        ('cap-wrong-rank',{'GUARDCERT_RECTANGULAR_CAPS':'16,16'},0),
        ('wrong-coordinate',{'GUARDCERT_POINT_NORMALIZATION':'wrong-coordinate'},0),
        ('wrong-bound',{'GUARDCERT_BOUND_NORMALIZATION':'wrong-bound'},0),
        ('scheduler-refusal',{'GUARDCERT_DOUBLE_TILING_MODE':'refuse'},0),
        ('private-refusal',{'GUARDCERT_DOUBLE_PRIVATE_COUNT':'1'},0),
        ('unit-tiles',{'GUARDCERT_TILE_SIZES':'1,1,1'},1),
        ('mixed-unit-tiles',{'GUARDCERT_TILE_SIZES':'1,32,1'},1)]:
        variants.append((name,text,options,sites,controls))
    variants.append(('unmarked',text.replace('#pragma scop\n','').replace('#pragma endscop\n',''),{},0,controls))
    text, _ = variant(5,7,9)
    start = text.index('#pragma scop'); end = text.index('#pragma endscop')+len('#pragma endscop')
    region = text[start:end]
    variants.append(('multiple-marked',text[:end]+'\n'+region+text[end:],{},2,None))
    variants.append(('marked-and-unmarked',text[:end]+'\n'+region.replace('#pragma scop','')
                     .replace('#pragma endscop','')+text[end:],{},1,None))
    if args.cases:
        selected = set(args.cases)
        if not selected <= {case[0] for case in variants}:
            raise ValueError('Unknown independent-bound context case')
        variants = [case for case in variants if case[0] in selected]
    work = ROOT / 'build/runtime-double-tile-bounds/rank-three-context-attempts' / args.attempt
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
                'runtime_bound_changes':[int(value) for value in re.findall(r'^GUARDCERT_RUNTIME_BOUNDS changed=(\d+)',trace,re.M)]}
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
        row['passed'] = (actual==expected_sites and row.get('digest_matches_GCC',False)
                         and (controls is None or row.get('public_controls')==[controls]))
        if expected_sites:
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
              'original_matmul_IEEE_operations_and_arrays_retained':True,
              'disclosed_variants_are_not_original_corpus_coverage':True,
              'independent_parameters_and_public_exits_checked':True,
              'actual_runtime_dispatch_established_by_output_alone':False,
              'controlled_cost_evidence_added':False,'full_goal_complete':False,'bindings':bindings}
    (work / 'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if report['status']!='passed':raise SystemExit(1)

if __name__=='__main__':main()
