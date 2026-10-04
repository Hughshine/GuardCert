"""Exercise every service in the same extracted, proved whole-program compiler."""
from pathlib import Path
import hashlib, json, os, subprocess
import native_affine_nest as deep
import native_memory_signed_multiple_pointers as rectangular
from native_zero_trip import function_body

ROOT = deep.ROOT
SOURCE = ROOT / 'examples/native_guardcert.c'
WORK = ROOT / 'build/native-guardcert'
COMPILER = ROOT / 'build/compcert-guardcert/ccomp'
SIGNED = [-2**31, -1073741825, -1073741824, -1, 0, 1, 1073741823, 1073741824, 2**31-1]
UNSIGNED = [0, 1, 2**31-1, 2**31, 2**32-2, 2**32-1]

def scalar_model():
    lines = []
    for value in SIGNED:
        product = deep.word(2*value)
        quotient = abs(product)//2 * (-1 if product < 0 else 1)
        lines.append(f'signed {value} {quotient}\n')
    for value in UNSIGNED:
        lines.append(f'unsigned {value} {11 if value == 2**32-1 else 22}\n')
    return ''.join(lines)

def generate():
    parts = [path.read_text().split('int main(void)', 1)[0]
             for path in [deep.SOURCE, rectangular.SOURCE]]
    parts.append('int guarded_signed(int x){return (x*2)/2;}\n'
                 'unsigned guarded_unsigned(unsigned x){if(x+1U<x)return 11U;else return 22U;}\n'
                 'int main(void){\n')
    parts += [f'affine_case({",".join(map(deep.literal,row))});\n' for row in deep.full_inputs()]
    parts += [f'signed_case({",".join(map(deep.literal,row))});\n' for row in rectangular.full_inputs()]
    parts += [f'printf("signed %d %d\\n",{deep.literal(x)},guarded_signed({deep.literal(x)}));\n' for x in SIGNED]
    parts += [f'printf("unsigned %u %u\\n",{x}U,guarded_unsigned({x}U));\n' for x in UNSIGNED]
    SOURCE.write_text(''.join(parts)+'return 0;}\n')

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_build():
    stamp = json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint'] == 'AffineNestUnifiedCompiler.compile_guardcert'
    assert stamp['compiler_sha256'] == sha(COMPILER)
    for path, digest in (stamp['proof_sources'] | stamp['native_sources']).items():
        assert sha(ROOT/path) == digest, path
    proof_path = ROOT/'build/affine-nest-foundation-prototype-report.json'
    assert stamp['prototype_proof_report_sha256'] == sha(proof_path)
    assert json.loads(proof_path.read_text())['unified_whole_program_assumptions_match_baseline']
    return stamp

def compile_run(name, mode, syntax, extra, expected):
    work = WORK/name; work.mkdir(parents=True, exist_ok=True)
    candidate = work/'candidate.sexp'; candidate.write_text('(interval (per-axis '+syntax+'))\n')
    env = {k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
    env |= {'GUARDCERT_AFFINE_MODE':mode, 'GUARDCERT_AFFINE_PROFILE':'inferred',
            'GUARDCERT_AFFINE_DIAGNOSTICS':'1', 'GUARDCERT_LOOP_CANDIDATE':str(candidate)} | extra
    with (work/'compile.log').open('w') as log:
        result = subprocess.run([str(COMPILER), '-conf', str(COMPILER.parent/'compcert.ini'),
            '-stdlib', str(COMPILER.parent/'runtime'), '-dclight', '-S', '-o', str(work/'program.s'),
            str(SOURCE)], cwd=work, env=env, stdout=log, stderr=subprocess.STDOUT, timeout=600)
    assert result.returncode == 0, (name, (work/'compile.log').read_text()[-3000:])
    subprocess.run(['gcc','-no-pie',str(work/'program.s'),'-o',str(work/'program')],check=True,capture_output=True)
    actual = subprocess.check_output([str(work/'program')],text=True,timeout=120)
    assert actual == expected, name
    (work/'output.txt').write_text(actual)
    dump_path = work/(SOURCE.stem+'.light.c'); dump = dump_path.read_text()
    deep_found = [fn for fn,d in zip(deep.NAMES,deep.DEPTHS) if function_body(dump,fn).count('for (') > d]
    rectangular_found = rectangular.observed_functions(dump)
    scalar_bodies = {fn:function_body(dump,fn) for fn in ['guarded_signed','guarded_unsigned']}
    # Installation is checked independently of equivalent program outputs.
    assert 'long long' in scalar_bodies['guarded_signed'], scalar_bodies
    assert scalar_bodies['guarded_unsigned'].count('if (') >= 2, scalar_bodies
    return {'actual_calls':len(deep.full_inputs())+len(rectangular.full_inputs())+len(SIGNED)+len(UNSIGNED),
        'deep_guarded_functions':deep_found, 'rectangular_guarded_functions':rectangular_found,
        'conditional_scalar_rewrites_installed':True, 'all_arrays_and_public_controls_match_models':True,
        'assembly_sha256':sha(work/'program.s'), 'clight_sha256':sha(dump_path),
        'output_sha256':sha(work/'output.txt'), 'compile_log_sha256':sha(work/'compile.log')}

def main():
    generate(); WORK.mkdir(parents=True, exist_ok=True)
    expected = (''.join(deep.output_model(row) for row in deep.full_inputs())
                + ''.join(rectangular.output_model(row) for row in rectangular.full_inputs()) + scalar_model())
    rectangular.common.checked_reference(SOURCE, WORK, expected)
    stamp = check_build()
    print('unified reference agrees with all word models', flush=True)
    identity = '(schedule ((coordinate 0) (coordinate 1) ordinal) ())'
    interchange = '(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))'
    invalid = '(schedule ((coordinate 99) ordinal) ())'
    options = [('disabled','disabled',invalid,{}), ('identity','identity',identity,{}),
               ('interchange','interchange',interchange,{}), ('tile-2-3','tile-2-3','(tile 2 3)',{}),
               ('wrong-deep-witness','wrong-tiling-witness',interchange,{}),
               ('resource-limit','interchange',interchange,{'GUARDCERT_FM_ROWS':'0'})]
    configurations = {}
    for name, mode, syntax, extra in options:
        row = compile_run(name,mode,syntax,extra,expected)
        if name in ['disabled','resource-limit']:
            assert not row['deep_guarded_functions'] and not row['rectangular_guarded_functions'], row
        elif name == 'identity':
            assert set(row['deep_guarded_functions']) == set(deep.NAMES), row
        elif name == 'wrong-deep-witness':
            assert not row['deep_guarded_functions'] and row['rectangular_guarded_functions'], row
        else:
            assert set(row['deep_guarded_functions']) == set(deep.NAMES)-{'affine_chain2'}, row
            assert row['rectangular_guarded_functions'], row
        configurations[name] = row
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name, row['deep_guarded_functions'], list(row['rectangular_guarded_functions']), flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'entrypoint':stamp['proved_entrypoint'],'source_sha256':sha(SOURCE),'configurations':configurations,
        'scope':'actual CompCert assembly of one C program using all three checked services'},indent=2)+'\n')

if __name__ == '__main__':
    main()
