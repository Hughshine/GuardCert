"""Check witness search, refusals and actual contexts on newly reached original cases."""
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
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a new simple attempt name')
    bindings = {}
    build = checked(ROOT / args.compiler_report, bindings)
    if build['status'] != 'built' or not build['proof_and_entrypoint_unchanged']:
        raise ValueError('Expected the audited successor driver')
    compiler = ROOT / build['compiler']
    work = ROOT / 'build/double-witness-policy/check-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    cases = []
    for case, sites in [('matmul-seq', 2), ('matmul-seq3', 3), ('tce', 4)]:
        source = permitted(ROOT / 'build/benchmark-alignment/probe-v1' / case / 'marked.c')
        bindings[str(source.relative_to(ROOT))] = sha(source)
        text = source.read_text()
        for label, mode, options in [('wrong-witness', 'wrong-witness', {}),
                ('two-axes', 'affine', {'GUARDCERT_DOUBLE_WITNESS_AXES': '2'}),
                ('scheduler-refusal', 'refuse', {})]:
            cases.append((case+'-'+label, mode, text, sites, 0, options))
        if case != 'matmul-seq':
            continue
        bound = int(re.search(r'long long N = (\d+);', text)[1])
        dynamic = text.replace('static const long long', 'static long long').replace(
            '  init_data();', '  init_data();\n  N = (int)polcert_rotr32((unsigned int)N, 16);\n'
            '  N = (int)polcert_rotr32((unsigned int)N, 16);')
        for label, value in [('positive', bound), ('zero', 0), ('negative', -1)]:
            changed = dynamic.replace('long long N = '+str(bound)+';', 'long long N = '+str(value)+';')
            cases.append((case+'-dynamic-'+label, 'affine', changed, sites, sites, {}))
        first, last = text.index('#pragma scop'), text.index('#pragma endscop')+len('#pragma endscop')
        selected = text[first:last]
        for label, second, installed in [('multiple-marked', selected, 4),
                ('marked-and-unmarked', selected.replace('#pragma scop', '').replace('#pragma endscop', ''), 2)]:
            cases.append((case+'-'+label, 'affine', text[:last]+'\n'+second+text[last:], 2, installed, {}))
        shared = selected
        for name in ['i', 'j', 'k']:
            shared = shared.replace('for (long long '+name, 'for ('+name)
        public = dynamic[:dynamic.index('#pragma scop')]+'long long i=17, j=23, k=29;\n'+shared+\
            '\nprintf("controls=%lld,%lld,%lld\\n",i,j,k);\n'+dynamic[dynamic.index('#pragma endscop')+len('#pragma endscop'):]
        for label, value in [('positive', bound), ('zero', 0), ('negative', -1)]:
            changed = public.replace('long long N = '+str(bound)+';', 'long long N = '+str(value)+';')
            cases.append((case+'-public-'+label, 'affine', changed, 2, 2, {}))
        cases.append((case+'-private-refusal', 'affine', text, 0, 0, {'GUARDCERT_DOUBLE_PRIVATE_COUNT': '1'}))
    rows = []
    for name, mode, text, calls, installed, options in cases:
        directory = work / name
        directory.mkdir()
        source = directory / 'program.c'
        source.write_text(text)
        env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE=mode, GUARDCERT_PLUTO=str(PLUTO),
            GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1', **options)
        compile_result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
            '-dclight', '-S', '-o', str(directory / 'program.s'), str(source)], directory, 'compiler', env)
        found = re.findall(r'GUARDCERT_DOUBLE_INSTALLED original=\d+ initialized=\d+ regions=(\d+) pipeline_calls=(\d+)',
            (out+err).decode(errors='replace'))
        actual = list(map(int, found[-1])) if found else None
        row = {'case': name, 'compiler': compile_result, 'mode': mode, 'policy_options': options,
            'expected_installed_and_calls': [installed, calls], 'installed_and_calls': actual}
        if compile_result['returncode'] == 0:
            link, _, _ = run(['gcc', '-no-pie', str(directory / 'program.s'), '-lm', '-o', str(directory / 'program')], directory, 'link')
            gcc, _, _ = run(['gcc', '-O0', '-ffp-contract=off', str(source), '-lm', '-o', str(directory / 'reference')], directory, 'gcc')
            row.update(link=link, gcc=gcc)
            if link['returncode'] == gcc['returncode'] == 0:
                native, output, _ = run([str(directory / 'program')], directory, 'native')
                reference, expected, _ = run([str(directory / 'reference')], directory, 'reference')
                row.update(native=native, reference=reference,
                    digest_matches_GCC=native['returncode'] == reference['returncode'] == 0 and output == expected)
                if '-public-' in name:
                    row['public_controls'] = re.findall(r'controls=([^\n]+)', output.decode())
        row['passed'] = actual == [installed, calls] and row.get('digest_matches_GCC', False)
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row, indent=2)+'\n')
        print(json.dumps({key: row[key] for key in ['case', 'passed', 'installed_and_calls']}), flush=True)
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected', 'cases': rows,
        'bindings': bindings, 'whole_program_entrypoint': build['whole_program_entrypoint'],
        'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'new_semantic_proofs_or_axioms': False, 'guard_branch_observation': False,
        'controlled_cost_comparison': False, 'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
