"""Execute schedules generated from actual source PolyLang in complete C programs."""
import hashlib
import json
import os
import re
import subprocess

import native_memory_multiarray as arrays
import native_memory_ragged as ragged

ROOT=arrays.ROOT
WORK=ROOT/'build/native-memory-schedules'
TEMPLATES=ROOT/'examples/schedule-candidates'


def main():
    compiler=arrays.COMPILER
    stamp=json.loads((compiler.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==arrays.ENTRY
    assert stamp['compiler_sha256']==hashlib.sha256(compiler.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    configurations={}
    for family,module,accepted in [('arrays',arrays,arrays.ACCEPTED),('ragged',ragged,ragged.ACCEPTED|{'ragged_other_bound'})]:
        module.WORK=WORK/family;module.WORK.mkdir(parents=True,exist_ok=True)
        subprocess.run(['gcc','-O0',str(module.SOURCE),'-o',str(module.WORK/'gcc-reference')],
                       check=True,capture_output=True)
        reference=subprocess.check_output([str(module.WORK/'gcc-reference')],text=True)
        assert reference==module.expected_output()
        (module.WORK/'gcc-output.txt').write_text(reference)
        cases=[(name,{},accepted-{'multi_three'} if name=='fission' else accepted)
               for name in ['identity','interchange','fission','shift','skew']]
        cases += [(name,{},set()) for name in ['wrong-map','empty-schedule','overflow-coefficient']]
        cases += [('reverse-dependent',{},
                   {'multi_cross_read_only','multi_copy_read_only'} if family=='arrays'
                   else {'ragged_write','ragged_copy','ragged_other_bound'})]
        cases += [('constant-schedule',{},None),('explicit-identity',{},
                  {'multi_two','multi_global','multi_enclosing','multi_cross_chain','multi_copy_chain'}
                  if family=='arrays' else {'ragged_two','ragged_prefix','ragged_chain','ragged_context'})]
        cases += [(name,extra,set()) for name,extra in
                  [('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),
                   ('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
        configurations[family]={}
        for name,extra,expected in cases:
            template='identity' if name in ['resource-limit','invalid-certificate'] else name
            dump=module.compile_run(name,{'GUARDCERT_LOOP_CANDIDATE':str(TEMPLATES/(template+'.sexp'))}|extra)
            observed=set()
            for function in accepted:
                body=module.function_body(dump,function)
                guarded='switch (0)' in body
                if expected is not None:
                    assert guarded==(function in expected),(family,name,function,body)
                if guarded:
                    observed.add(function)
                    assert '$i = $n;' in body,(family,name,function,'public row exit')
                    assert ('$j = $k;' if family=='ragged' else '$j = $m;') in body, (family,name,function,'public column exit')
                    if family=='arrays' or function not in {'ragged_write', 'ragged_other_bound'}:
                        assert re.search(r'if \([^\n]* != [^\n]*\)',body), (family,name,function,'safe actual array comparison')
            refused=arrays.REFUSED if family=='arrays' else set()
            for function in refused:
                assert 'switch (0)' not in module.function_body(dump,function),(family,name,function)
            configurations[family][name]={'guarded_functions':sorted(observed),
                'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
                'template_sha256':hashlib.sha256((TEMPLATES/(template+'.sexp')).read_bytes()).hexdigest()}
    report={'status':'passed','proved_entrypoint':arrays.ENTRY,'compiler_sha256':stamp['compiler_sha256'],
            'configurations':configurations,'actual_source_extraction_and_schedule_generation':True,
            'generated_loop_independently_checked':True,'generator_alarm_falls_back':True,
            'real_compcert_arrays_and_full_program_context':True,'general_c_source_grammar_supported':False}
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print('Source-to-schedule-to-generated-Loop-to-C-to-Asm passed in both source families')


if __name__=='__main__':main()
