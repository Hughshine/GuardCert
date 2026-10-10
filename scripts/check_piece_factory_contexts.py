"""Check disclosed whole-fusion variants in callers, continuations and repeated sites."""
import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from observe_piece_fusion import store_loops
from probe_piece_models import checked, run, PLUTO

BUILD = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-factory-v2/report.json'
INPUT = ROOT / 'build/benchmark-alignment/probe-v1/fusion2/marked.c'
PORTABLE = ROOT / 'docs/piece-factory-contexts.json'


def selected_groups(path):
    text = permitted(path).read_text()
    result = []
    for label in re.finditer(r'\b__guardcert_scop_\d+:', text):
        tail = text[label.end():]
        end = re.search(r'\bguardcert_after\(\s*(\d+)(?:LL)?\s*\);', tail)
        if not end:
            raise ValueError('Missing disclosed continuation after the selected region')
        result.append({'continuation_tag': int(end.group(1)), 'stores': store_loops(tail[:end.start()])})
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(BUILD, bindings)
    if not build['data_only_piece_proposer_consumed_by_actual_factory'] or build['piece_checks_diagnostic_only']:
        raise ValueError('Require the actual piece factory')
    compiler = permitted(ROOT/build['compiler'])
    original = permitted(INPUT).read_text()
    bindings[str(INPUT.relative_to(ROOT))] = sha(INPUT)
    start = original.index('#pragma scop')
    end = original.index('#pragma endscop') + len('#pragma endscop')
    region = original[start:end]
    before, after = original[:start], original[end:]
    marker = 'static void guardcert_after(long long tag) { printf("tag=%lld\\n",tag); }\n'

    def finish(text):
        return text.replace('int main(void)', marker+'\nint main(void)', 1)

    first = region+'\nguardcert_after(1LL);\n'
    variants = [
        ('multiple-marked', finish(before+first+region+'\nguardcert_after(2LL);\n'+after), {}, 2, None),
        ('marked-and-unmarked', finish(before+first+region.replace('#pragma scop', '')
            .replace('#pragma endscop', '')+'\nguardcert_after(2LL);\n'+after), {}, 1, None),
        ('halo-continuation', finish(before+'A[102][2]=3.25;\n'+first
            +'printf("halo=%.17g\\n",A[102][2]+B[101][101]);\n'+after), {}, 1, None),
        ('enclosing-conditional', finish(before+'if (A[0][0]>-1000.0) {\n'+first+'}\n'+after), {}, 1, None),
        ('private-pool-refusal', finish(before+first+after), {'GUARDCERT_DOUBLE_PRIVATE_COUNT': '1'}, 0, None),
    ]
    public = region.replace('for (long long x', 'for (x').replace('for (long long y', 'for (y')
    variants.append(('public-iterators', finish(before+'long long x=17,y=23;\n'+public
        +'\nguardcert_after(1LL);\nprintf("controls=%lld,%lld\\n",x,y);\n'+after), {}, 1, 'controls=100,100'))
    helper = marker+'\nstatic void guardcert_kernel(void) {\n'+first+'}\n'
    caller = original[:start]+'long long cookie=71;\nguardcert_kernel();\n'
    caller += 'printf("cookie=%lld\\n",cookie);\n'+after
    caller = caller.replace('int main(void)', helper+'\nint main(void)', 1)
    variants.append(('caller-live-temp', caller, {}, 1, 'cookie=71'))
    work = ROOT/'build/piece-factory/context-attempts'/args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    rows = []
    for name, text, options, expected_fusions, expected_line in variants:
        case_dir = work/name
        case_dir.mkdir()
        source = case_dir/'variant.c'
        source.write_text(text)
        gcc, _, _ = run(['gcc', '-O0', '-ffp-contract=off', str(source), '-lm',
            '-o', str(case_dir/'reference')], case_dir, 'gcc')
        reference, expected, _ = run([str(case_dir/'reference')], case_dir, 'reference') if gcc['returncode'] == 0 else ({'returncode': None}, b'', b'')
        for mode in ['untiled', 'tiled']:
            directory = case_dir/mode
            directory.mkdir()
            current = directory/'program.c'
            current.write_bytes(source.read_bytes())
            env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
                GUARDCERT_PHASE_KIND=mode, GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='4096',
                GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1')
            env.update(options)
            compile_result, _, _ = run([str(compiler), '-fall', '-stdlib', str(compiler.parent/'runtime'),
                '-dclight', '-S', '-o', str(directory/'program.s'), str(current)], directory, 'compiler', env)
            row = {'case': name, 'mode': mode, 'input_sha256': sha(current), 'options': options,
                'gcc': gcc, 'reference': reference, 'compiler': compile_result,
                'expected_whole_fusions': expected_fusions, 'expected_observation_line': expected_line}
            if compile_result['returncode'] == 0:
                link, _, _ = run(['gcc', '-no-pie', str(directory/'program.s'), '-lm',
                    '-o', str(directory/'program')], directory, 'link')
                row['link'] = link
                if link['returncode'] == 0:
                    native, actual, _ = run([str(directory/'program')], directory, 'native')
                    groups = selected_groups(directory/'program.light.c')
                    count = sum(bool(group['stores']['shared_A_B_loops']) for group in groups)
                    row.update(native=native, selected_store_groups=groups, actual_whole_fusions=count,
                        complete_output_matches=reference['returncode'] == native['returncode'] == 0 and expected == actual,
                        expected_line_present=expected_line is None or expected_line in actual.decode().splitlines())
            row['passed'] = bool(row.get('complete_output_matches') and row.get('expected_line_present')
                and row.get('actual_whole_fusions') == expected_fusions)
            rows.append(row)
            (directory/'row.json').write_text(json.dumps(row, indent=2)+'\n')
            print(json.dumps({k:row.get(k) for k in ['case', 'mode', 'passed', 'actual_whole_fusions']}), flush=True)
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected',
        'compiler_entrypoint': build['whole_program_entrypoint'], 'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'original_case': 'fusion2', 'original_input_sha256': sha(INPUT),
        'all_sources_are_disclosed_context_variants': True,
        'original_arrays_and_numeric_kernel_retained': True, 'cases': rows, 'configuration_count': len(rows),
        'runtime_guard_refusal_exercised': False, 'controlled_cost_comparison': False,
        'full_goal_complete': False, 'bindings': bindings}
    filename = 'report.json' if report['status'] == 'passed' else 'rejection.json'
    if report['status'] == 'passed':
        portable = {k:v for k,v in report.items() if k != 'bindings'}
        portable['report'] = str((work/filename).relative_to(ROOT))
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable, indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (work/filename).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'configurations': len(rows), 'bindings': len(bindings)}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
