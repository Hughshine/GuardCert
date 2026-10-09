"""Check actual runtime-header accesses, conservative refusal and selected program contexts.

These disclosed variants retain fusion5's arrays, complete observation and both
nests. They supplement, rather than replace, replay of the unchanged original.
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
    if not build.get('selected_actual_Clight_literal_normalization_extracted_and_called'):
        raise ValueError('Expected actual checked literal-normalization compiler')
    compiler = permitted(ROOT / build['compiler'])
    input_path = permitted(ROOT / 'build/benchmark-alignment/probe-v1/fusion5/marked.c')
    bindings[str(input_path.relative_to(ROOT))] = sha(input_path)
    original = input_path.read_text()
    old = '(2 * A[((i) + 2)][((j) + 2)])'
    read = 'A[((i) + 2)][((j) + 2)]'
    if original.count(old) != 1:
        raise ValueError('Pinned first assignment changed')
    small = original.replace('static const long long N = 96;', 'static long long N = 64;')
    assert small != original
    dynamic = small.replace('  init_data();', '  init_data();\n'
        '  N = (int)polcert_rotr32((unsigned int)N, 16);\n'
        '  N = (int)polcert_rotr32((unsigned int)N, 16);')
    variants = [
        ('signed-i32', small, {}, 1, None),
        ('signed-i64', small.replace(old, '(2LL * '+read+')'), {}, 1, None),
        ('signed-i32-max', small.replace(old, '(2147483647 * '+read+')'), {}, 1, None),
        ('signed-i64-rounding', small.replace(old, '(9223372036854775807LL * '+read+')'), {}, 1, None),
        ('mixed-operation-tree', small.replace(old, '(((2 * '+read+') + 3) / 5LL)'), {}, 1, None),
        ('subtraction', small.replace(old, '(3 - '+read+')'), {}, 1, None),
        ('floating-negation', small.replace(old, '(-(2 * '+read+'))'), {}, 1, None),
        ('negative-zero', small.replace(old, '(-(0 * '+read+'))'), {}, 1, None),
        ('unsigned-refusal', small.replace(old, '(2U * '+read+')'), {}, 0, None),
        ('integer-subtree-refusal', small.replace(old, '((2 * (i + 1)) * '+read+')'), {}, 0, None),
        ('wrong-coordinate', small, {'GUARDCERT_POINT_NORMALIZATION': 'wrong-coordinate'}, 0, None),
        ('scheduler-refusal', small, {'GUARDCERT_DOUBLE_TILING_MODE': 'refuse'}, 0, None),
        ('private-refusal', small, {'GUARDCERT_DOUBLE_PRIVATE_COUNT': '1'}, 0, None),
        ('unmarked', small.replace('#pragma scop\n', '').replace('#pragma endscop\n', ''), {}, 0, None),
    ]
    for name, value in [('zero', 0), ('negative', -1), ('below-tile', 31), ('at-tile', 32), ('above-tile', 33)]:
        variants.append(('dynamic-'+name,
            dynamic.replace('long long N = 64;', 'long long N = '+str(value)+';'), {}, 1, None))
    start = dynamic.index('#pragma scop')
    end = dynamic.index('#pragma endscop') + len('#pragma endscop')
    selected = dynamic[start:end]
    for name, second, count in [('multiple-marked', selected, 2),
                              ('marked-and-unmarked', selected.replace('#pragma scop', '').replace('#pragma endscop', ''), 1)]:
        variants.append((name, dynamic[:end]+'\n'+second+dynamic[end:], {}, count, None))
    shared = selected.replace('for (long long i', 'for (i').replace('for (long long j', 'for (j')
    public = dynamic[:start]+'long long i=17, j=23;\n'+shared+\
        '\nprintf("controls=%lld,%lld\\n",i,j);\n'+dynamic[end:]
    for name, value, controls in [('positive', 64, '64,64'), ('zero', 0, '0,23'), ('negative', -1, '0,23')]:
        variants.append(('public-'+name,
            public.replace('long long N = 64;', 'long long N = '+str(value)+';'), {}, 1, controls))
    second_index = '((N - j) + 2)'
    assert small.count(second_index)==1
    variants += [
        ('parameter-reassociated', dynamic.replace(second_index, '((N + 1) - j + 1)'), {}, 1, None),
        ('parameter-cancellation', dynamic.replace(second_index, '((N - j) + 2 + (i - i))'), {}, 1, None),
        ('nonlinear-zero-refusal', dynamic.replace(second_index, '((N - j) + 2 + (i * j * 0))'), {}, 1, None),
        ('independent-header-refusal', dynamic.replace('static long long N = 64;',
            'static long long N = 64;\nstatic long long M = 64;').replace(second_index, '((M - j) + 2)'), {}, 1, None),
        ('upper-accepted-count', dynamic.replace('long long N = 64;', 'long long N = 98;'), {}, 1, None),
        ('unit-tiles', dynamic, {'GUARDCERT_TILE_SIZES':'1,1'}, 1, None),
        ('mixed-unit-tiles', dynamic, {'GUARDCERT_TILE_SIZES':'1,32'}, 1, None),
    ]
    refused = {'wrong-coordinate','scheduler-refusal','private-refusal','unmarked'}
    variants = [(name,text,options,
                 0 if name in refused else count+(2 if name=='multiple-marked' else 1),controls)
                for name,text,options,count,controls in variants]
    # A refused parameter-index source leaves the old first-nest route available.
    variants = [(name,text,options,1 if name in {'nonlinear-zero-refusal','independent-header-refusal'} else count,controls)
                for name,text,options,count,controls in variants]
    if args.cases:
        requested = set(args.cases)
        if not requested <= {case[0] for case in variants}:
            raise ValueError('Unknown literal/context case')
        variants = [case for case in variants if case[0] in requested]
    work = ROOT / 'build/double-header-access/context-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    rows = []
    for name, text, options, expected_sites, controls in variants:
        directory = work / name
        directory.mkdir()
        source = directory / 'program.c'
        source.write_text(text)
        env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
                   GUARDCERT_TILE_SIZES='32', GUARDCERT_PLUTO=str(PLUTO),
                   GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1')
        env.update(options)
        result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
            '-dclight', '-S', '-o', str(directory / 'program.s'), str(source)], directory, 'compiler', env)
        trace = (out+err).decode(errors='replace')
        tags = re.findall(r'GUARDCERT_QUOTIENT_TILING_INSTALLED regions=(\d+) older_reduction_regions=(\d+) divisor=(\d+)', trace)
        actual = list(map(int, tags[-1])) if tags else None
        header_tags=re.findall(r'GUARDCERT_HEADER_QUOTIENT_INSTALLED regions=(\d+)',trace)
        actual_header=int(header_tags[-1]) if header_tags else None
        expected_header = 0 if name in refused or name in {'nonlinear-zero-refusal','independent-header-refusal'} else (2 if name=='multiple-marked' else 1)
        expected_divisor=min(map(int,options.get('GUARDCERT_TILE_SIZES','32').split(',')))
        row = {'header_installed':actual_header,'expected_header_sites':expected_header,
               'expected_divisor':expected_divisor,'case': name, 'compiler': result, 'options': options,
               'quotient_and_older_installed': actual, 'expected_quotient_sites': expected_sites,
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
        row['passed'] = (actual == [expected_sites, 0, expected_divisor] and actual_header==expected_header and row.get('digest_matches_GCC', False)
                         and (controls is None or row.get('public_controls') == [controls]))
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row, indent=2)+'\n')
        print(json.dumps({key: row[key] for key in ['case', 'passed', 'quotient_and_older_installed','header_installed']}), flush=True)
    for path in [Path(__file__), PLUTO, *[path for path in work.rglob('*') if path.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected',
        'cases': rows, 'bindings': bindings, 'compiler_entrypoint': build['whole_program_entrypoint'],
        'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'original_case': 'fusion5', 'all_sources_are_disclosed_context_variants': True,
        'complete_original_arrays_and_observation_retained': True,
        'actual_header_parameter_nest_installed_and_checked_separately': True,
        'unsupported_independent_parameter_and_nonlinear_accesses_refuse': True,
        'candidate_refusal_preserves_current_normalized_source': True,
        'actual_assembly_branch_observations_added': False, 'controlled_cost_comparison': False,
        'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'cases': len(rows)}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
