"""Check actual polynomial point recovery, refusal and whole-program contexts.

Inputs derive from the pinned C harness. Runtime-header and public-exit variants
are disclosed context tests; they do not count as additional original benchmarks.
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
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if not build.get('untrusted_generated_point_recovery') or not build['proof_and_entrypoint_unchanged']:
        raise ValueError('Expected the audited point-proposal compiler')
    compiler = permitted(ROOT / build['compiler'])
    source_path = permitted(ROOT / 'build/benchmark-alignment/probe-v1/polynomial/marked.c')
    bindings[str(source_path.relative_to(ROOT))] = sha(source_path)
    original = source_path.read_text()
    work = ROOT / 'build/generated-point-recovery/context-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    small = original.replace('static const long long n = 4096;', 'static long long n = 64;')
    assert small != original
    dynamic = small.replace('  init_data();', '  init_data();\n'
        '  n = (int)polcert_rotr32((unsigned int)n, 16);\n'
        '  n = (int)polcert_rotr32((unsigned int)n, 16);')
    cases = []
    for name, mode, options, sites, calls in [
        ('normalization-disabled', 'tile', {'GUARDCERT_POINT_NORMALIZATION': 'disabled'}, 0, 1),
        ('wrong-coordinate', 'tile', {'GUARDCERT_POINT_NORMALIZATION': 'wrong-coordinate'}, 0, 1),
        ('wrong-witness', 'wrong-witness', {}, 0, 1),
        ('malformed', 'malformed', {}, 0, 1),
        ('scheduler-refusal', 'refuse', {}, 0, 1),
        ('private-refusal', 'tile', {'GUARDCERT_DOUBLE_PRIVATE_COUNT': '1'}, 0, 0),
        ('unmarked', 'tile', {}, 0, 0),
    ]:
        text = small.replace('#pragma scop\n', '').replace('#pragma endscop\n', '') if name == 'unmarked' else small
        cases.append((name, mode, text, options, sites, calls, None))
    for label, value in [('positive', 64), ('zero', 0), ('negative', -1)]:
        text = dynamic.replace('long long n = 64;', 'long long n = '+str(value)+';')
        cases.append(('dynamic-'+label, 'tile', text, {}, 1, 1, None))
    first = dynamic.index('#pragma scop')
    last = dynamic.index('#pragma endscop') + len('#pragma endscop')
    selected = dynamic[first:last]
    for name, second, sites in [('multiple-marked', selected, 2),
                              ('marked-and-unmarked', selected.replace('#pragma scop', '').replace('#pragma endscop', ''), 1)]:
        cases.append((name, 'tile', dynamic[:last]+'\n'+second+dynamic[last:], {}, sites, sites, None))
    shared = selected.replace('for (long long i', 'for (i').replace('for (long long j', 'for (j')
    public = dynamic[:first]+'long long i=17, j=23;\n'+shared+\
        '\nprintf("controls=%lld,%lld\\n",i,j);\n'+dynamic[last:]
    for label, value, controls in [('positive', 64, '64,64'), ('zero', 0, '0,23'), ('negative', -1, '0,23')]:
        text = public.replace('long long n = 64;', 'long long n = '+str(value)+';')
        cases.append(('public-'+label, 'tile', text, {}, 1, 1, controls))
    renamed = re.sub(r'\bn\b', 'extent', dynamic)
    for old, new in [('8196', '8200'), ('4100', '4104'), ('12291', '12300')]:
        renamed = renamed.replace(old, new)
    cases.append(('renamed-and-resized', 'tile', renamed, {}, 1, 1, None))
    rows = []
    for name, mode, text, options, sites, calls, controls in cases:
        directory = work / name
        directory.mkdir()
        source = directory / 'program.c'
        source.write_text(text)
        env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE=mode,
                   GUARDCERT_TILE_SIZES='32', GUARDCERT_PLUTO=str(PLUTO),
                   GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1')
        env.update(options)
        result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
            '-dclight', '-S', '-o', str(directory / 'program.s'), str(source)], directory, 'compiler', env)
        trace = (out+err).decode(errors='replace')
        found = re.findall(r'GUARDCERT_DOUBLE_TILING_INSTALLED reduction=(\d+) phase_calls=(\d+)', trace)
        actual = list(map(int, found[-1])) if found else None
        row = {'case': name, 'mode': mode, 'options': options, 'compiler': result,
               'installed_and_phase_calls': actual, 'expected': [sites, calls],
               'point_proposals': [p.read_text() for p in sorted(directory.glob('tiling-pipeline-*/point-normalization.txt'))],
               'expected_public_controls': controls}
        if result['returncode'] == 0:
            link, _, _ = run(['gcc', '-no-pie', str(directory / 'program.s'), '-lm', '-o', str(directory / 'program')], directory, 'link')
            gcc, _, _ = run(['gcc', '-O0', '-ffp-contract=off', str(source), '-lm', '-o', str(directory / 'reference')], directory, 'gcc')
            row.update(link=link, gcc=gcc)
            if link['returncode'] == gcc['returncode'] == 0:
                native, output, _ = run([str(directory / 'program')], directory, 'native')
                reference, expected, _ = run([str(directory / 'reference')], directory, 'reference')
                row.update(native=native, reference=reference,
                    digest_matches_GCC=native['returncode'] == reference['returncode'] == 0 and output == expected)
                if controls is not None:
                    row['public_controls'] = re.findall(r'controls=([^\n]+)', output.decode())
        row['passed'] = (actual == [sites, calls] and row.get('digest_matches_GCC', False)
                         and (controls is None or row.get('public_controls') == [controls]))
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row, indent=2)+'\n')
        print(json.dumps({key: row[key] for key in ['case', 'passed', 'installed_and_phase_calls']}), flush=True)
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected',
        'cases': rows, 'bindings': bindings, 'compiler_entrypoint': build['whole_program_entrypoint'],
        'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'original_case': 'polynomial', 'context_bounds_are_disclosed_variants': True,
        'raw_to_normalized_equivalence_assumed': False, 'same_final_checker_and_proof': True,
        'guard_branch_observations_added': False, 'controlled_cost_comparison': False,
        'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'cases': len(rows), 'passed': sum(row['passed'] for row in rows)}))
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
