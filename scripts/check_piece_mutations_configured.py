"""Check original piece witnesses and reject mutated actual-domain proposals."""
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_diagnostics import checked

WORK = ROOT / 'build/piece-family/mutations-v2'
NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-receipts-v1/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-diagnostic-attempts/fusion2-v2/report.json'
PORTABLE = ROOT / 'docs/piece-mutations.json'


def main():
    bindings = {}
    build, replay = [checked(path, bindings) for path in [NATIVE, REPLAY]]
    if not build['piece_checks_diagnostic_only'] or replay['native_configuration_matches'] != 3:
        raise ValueError('Require the actual domain-only compiler replay')
    compiler_work = (ROOT / build['compiler']).parent
    WORK.mkdir(parents=True, exist_ok=False)
    code = ['module PF = GuardMemoryDoublePieceFamily.DoublePieceFamily',
            'module PC = PolCertPieceCoordinates',
            'let rec nat n = if n=0 then Datatypes.O else Datatypes.S (nat (n-1))',
            'let integer value = GuardMemoryNumbers.import_integer (Z.of_string value)',
            'let checked operation = let result=ref None in',
            '  ImpureConfig.Core.Base.bind operation (fun (accepted,alarm_free)->result:=Some (accepted,alarm_free));',
            '  match !result with Some (accepted,true)->accepted | _->false',
            'let mutate_last rows = match List.rev rows with []->invalid_arg "empty map"',
            ' | (row,bias)::rest -> List.rev ((row,BinInt.Z.add bias (integer "1"))::rest)',
            'let inspect mode parent width domain pieces witness =',
            '  let valid=checked (PF.check_piece_family (nat width) domain pieces witness) in',
            '  let first=List.hd pieces in',
            '  let wrong_project={first with PC.piece_project=mutate_last first.PC.piece_project} in',
            '  let wrong_embed={first with PC.piece_embed=mutate_last first.PC.piece_embed} in',
            '  let project_refused=not (checked (PF.K.check_piece_coordinates (nat width) domain wrong_project)) in',
            '  let embed_refused=not (checked (PF.K.check_piece_coordinates (nat width) domain wrong_embed)) in',
            '  let missing_refused=not (checked (PF.check_piece_family (nat width) domain (List.tl pieces) witness)) in',
            '  let duplicate_refused=not (checked (PF.check_piece_family (nat width) domain (pieces@[first]) witness)) in',
            '  Printf.printf "{\\\"mode\\\":\\\"%s\\\",\\\"parent\\\":%d,\\\"valid\\\":%b,\\\"wrong_project_refused\\\":%b,\\\"wrong_embed_refused\\\":%b,\\\"missing_piece_refused\\\":%b,\\\"duplicate_piece_refused\\\":%b}\\n%!"',
            '    mode parent valid project_refused embed_refused missing_refused duplicate_refused;',
            '  if not (valid && project_refused && embed_refused && missing_refused && duplicate_refused) then exit 1']
    # Literal proposal data is emitted from actual receipts, without changing
    # the extracted checker or its native certificate search.
    def integer(value):
        return 'integer "' + str(value) + '"'
    def rows(values):
        return '[' + ';'.join('([' + ';'.join(map(integer, row)) + '],' + integer(bias) + ')'
                              for row, bias in values) + ']'
    def witness(value):
        if 'piece' in value:
            return f'PF.D.CoverPiece (nat {value["piece"]})'
        if 'empty' in value:
            return 'PF.D.CoverEmpty'
        row, bias = value['split']
        affine = '([' + ';'.join(map(integer, row)) + '],' + integer(bias) + ')'
        return f'PF.D.CoverSplit ({affine},({witness(value["yes"])}),({witness(value["no"])}))'
    for mode, count in [('untiled', 6), ('tiled', 7)]:
        phase = REPLAY.parent / 'fusion2-original' / mode / 'tiling-pipeline-1'
        pieces = [json.loads(permitted(phase / f'piece-{i}.json').read_text()) for i in range(count)]
        for parent in [0, 1]:
            family = [p for p in pieces if p['parent'] == parent]
            certificate = json.loads(permitted(phase / f'piece-parent-{parent}-witness.json').read_text())
            values = ['{PC.piece_domain=' + rows(p['candidate_domain']) + ';PC.piece_embed=' + rows(p['embed'])
                      + ';PC.piece_project=' + rows(p['project']) + '}' for p in family]
            code.append('let () = inspect "' + mode + f'" {parent} {family[0]["source_width"]} '
                        + rows(family[0]['source_domain']) + ' [' + ';'.join(values) + '] (' + witness(certificate) + ')')
    source = WORK / 'CheckPieces.ml'
    source.write_text('\n'.join(code).replace('\\\"', '\\"') + '\n')
    directories = [compiler_work / name for name in
                   ['extraction','lib','common','x86','backend','cfrontend','cparser','driver','export','debug']]
    objects = sorted(compiler_work.rglob('*.cmx'))
    modules = {p.stem[0].upper()+p.stem[1:]: p for p in objects if p.with_suffix('.ml').exists()}
    include = sum((['-I',str(path)] for path in directories), [])
    dependency = subprocess.run(['ocamldep','-modules',*include,str(source),
                                 *[str(p.with_suffix('.ml')) for p in modules.values()]],
                                capture_output=True,text=True,check=True)
    (WORK / 'dependencies.log').write_text(dependency.stdout+dependency.stderr)
    dependencies = {}
    for line in dependency.stdout.splitlines():
        path, names = line.split(':',1)
        dependencies[Path(path).stem[0].upper()+Path(path).stem[1:]] = names.split()
    ordered, seen = [], set()
    def visit(name):
        if name in seen or name not in modules:
            return
        seen.add(name)
        for child in dependencies[name]:
            visit(child)
        ordered.append(modules[name])
    for name in dependencies['CheckPieces']:
        visit(name)
    command = ['ocamlfind','ocamlopt','-linkpkg','-package','zarith',*include,
               'str.cmxa','unix.cmxa',*[str(p) for p in ordered],str(source),'-o',str(WORK/'check-pieces')]
    with (WORK/'compile.log').open('x') as log:
        compiled = subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,cwd=WORK)
    if compiled.returncode:
        (WORK/'rejection.json').write_text(json.dumps({'status':'rejected','stage':'compile',
            'command':command,'returncode':compiled.returncode})+'\n')
        raise ValueError((WORK/'compile.log').read_text()[-3000:])
    run = subprocess.run([str(WORK/'check-pieces'),'-conf',str(compiler_work/'compcert.ini')],capture_output=True,text=True,timeout=120)
    (WORK/'stdout.log').write_text(run.stdout); (WORK/'stderr.log').write_text(run.stderr)
    if run.returncode:
        (WORK/'rejection.json').write_text(json.dumps({'status':'rejected','stage':'run','returncode':run.returncode})+'\n')
        raise ValueError(run.stdout+run.stderr)
    outcomes = [json.loads(line) for line in run.stdout.splitlines()]
    if len(outcomes) != 4 or not all(all(v for k,v in row.items() if k not in {'mode','parent'}) for row in outcomes):
        raise ValueError('Require all four original families and mutated refusals')
    for path in [Path(__file__),compiler_work/'compcert.ini',*WORK.iterdir(),*[p.with_suffix(suffix) for p in ordered for suffix in ['.ml','.cmx','.cmi','.o']]]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'checked','actual_source_case':'fusion2-original','original_source_and_numeric_types_unchanged':True,
        'actual_extracted_piece_witnesses_reused':True,'outcomes':outcomes,'valid_family_checks':4,'mutated_refusals':16,
        'checker_semantics_overridden':False,'whole_fusion_installed':False,'instruction_order_and_Loop_bridge_proved':False,
        'full_goal_complete':False,'command':command,'bindings':bindings}
    portable = {k:v for k,v in report.items() if k not in {'bindings','command'}}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'checked','valid':4,'refused':16,'bindings':len(bindings)}))


if __name__ == '__main__':
    main()
