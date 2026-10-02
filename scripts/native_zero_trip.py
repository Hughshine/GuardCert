"""Check entire frontend for-loop replacement and its zero-trip memory barrier."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / 'build' / 'compcert-guard' / 'ccomp'
SOURCE = ROOT / 'examples' / 'native_zero_trip.c'
WORK = ROOT / 'build' / 'native-zero-trip'


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def function_body(dump, name):
    match = re.search(r'\b' + name + r'\([^;{}]*\)\s*\{', dump)
    if not match:
        raise SystemExit(f'function missing: {name}')
    depth = 1
    for index in range(match.end(), len(dump)):
        depth += (dump[index] == '{') - (dump[index] == '}')
        if not depth:
            return dump[match.end():index]
    raise SystemExit(f'function incomplete: {name}')


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run(COMPILER, '-conf', COMPILER.parent / 'compcert.ini', '-stdlib',
        COMPILER.parent / 'runtime', '-dclight', '-S', '-o', WORK / 'zero.s', SOURCE)
    run('gcc', WORK / 'zero.s', '-o', WORK / 'zero-native')
    run('gcc', '-O0', SOURCE, '-o', WORK / 'gcc-reference')
    actual = run(WORK / 'zero-native').stdout
    reference = run(WORK / 'gcc-reference').stdout
    if actual != reference:
        raise SystemExit(f'zero-trip behavior mismatch\n{actual}\n{reference}')
    pairs = [(0, 0), (1, 0), (-2, 1), (4, 7), (2**31-2, 2**31-1),
             (2**31-1, 2**31-1), (-2**31, -2**31), (-2**31, -2**31+1)]
    expected = ''.join(f'zero {start} {bound} {max(bound-start, 0)} '
                       f'{2*max(bound-start, 0)} {max(bound-start, 0)}\n'
                       for start, bound in pairs)
    expected += 'pointer 1 8 1\nexcluded 1 2\n'
    if actual != expected:
        raise SystemExit(f'zero-trip independent check failed\n{actual}\n{expected}')
    dumps = list(WORK.glob('*.light.c'))
    if len(dumps) != 1:
        raise SystemExit(f'expected one Clight dump: {dumps}')
    dump = dumps[0].read_text()
    inserted = {}
    for name in ['ordinary', 'loop_context', 'goto_context', 'zero_trip_null']:
        body = function_body(dump, name)
        # PrintClight prints Sloop as a for whose first body test breaks.
        pattern = r'if \(\$i < \$n\) \{\s*for \('
        count = len(re.findall(pattern, body))
        if count != 1:
            raise SystemExit(f'expected one whole-loop entry guard in {name}, got {count}\n{body}')
        if 'if (! ($i < $n))' not in body:
            raise SystemExit(f'original loop missing inside guarded branch: {name}')
        inserted[name] = count
    for name in ['counter_body_excluded', 'nonstrict_excluded']:
        body = function_body(dump, name)
        if re.search(r'if \(\$i < \$n\) \{\s*for \(', body):
            raise SystemExit(f'unsupported loop accepted: {name}')
    stamp = json.loads((COMPILER.parent / '.guard-build.json').read_text())
    if stamp['proved_entrypoint'] != 'AdaptiveRegionCompiler.compile_progress_regions':
        raise SystemExit('unexpected extracted compiler entrypoint')
    (WORK / 'output.txt').write_text(actual)
    (WORK / 'report.json').write_text(json.dumps({
        'proved_entrypoint': stamp['proved_entrypoint'], 'compiler_sha256': stamp['compiler_sha256'],
        'source': str(SOURCE), 'inputs': pairs, 'gcc_behavior_matches': True,
        'independent_iteration_counts_checked': True, 'whole_loop_guards': inserted,
        'whole_loop_replacement_in_actual_frontend_ast': True,
        'normal_loop_and_goto_contexts_checked': True, 'positive_and_zero_trip_paths_checked': True,
        'zero_trip_null_body_pointer_checked': True, 'signed_extreme_boundaries_checked': True,
        'mutable_counter_and_nonstrict_condition_excluded': True,
        'performance_measured': False, 'polopt_optimizer_connected': False,
    }, indent=2) + '\n')
    print(f'Entire frontend loops passed: {len(pairs)} signed input pairs, '
          f'{sum(inserted.values())} whole-loop guards, null body barrier and refusals checked')


if __name__ == '__main__':
    main()
