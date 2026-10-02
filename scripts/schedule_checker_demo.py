"""Extract and run the semantics-independent verified schedule checker."""
from pathlib import Path
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "schedule-checker-demo"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Extract.v"
    source.write_text("""From Stdlib Require Import List Bool Arith Extraction ExtrOcamlBasic ExtrOcamlNatInt.
From Guard Require Import AbstractScheduleChecker.
Definition check_independent_indices :=
  @check_schedule nat Nat.eq_dec (fun a b => negb (Nat.eqb a b)).
Definition check_no_commutations := @check_schedule nat Nat.eq_dec (fun _ _ => false).
Extraction Language OCaml.
Extraction "Checker.ml" check_independent_indices check_no_commutations.
""")
    run("rocq", "compile", "-Q", ROOT / "theories", "Guard", source)
    (WORK / "Main.ml").write_text("""let rec selections = function
  | [] -> []
  | head :: tail -> (head,tail) :: List.map (fun (x,rest) -> x, head :: rest) (selections tail)
let rec permutations = function
  | [] -> [[]]
  | xs -> List.concat (List.map (fun (head,rest) ->
      List.map (fun tail -> head :: tail) (permutations rest)) (selections xs))
let source = [0;1;2;3;4]
let orders = permutations source
let require condition message = if not condition then failwith message
let () =
  List.iter (fun target -> require (Checker.check_independent_indices source target)
    "independent permutation rejected") orders;
  List.iter (fun target -> require (Checker.check_no_commutations source target = (target = source))
    "uncertified commutation accepted") orders;
  List.iter (fun target -> require (not (Checker.check_independent_indices source target))
    "malformed action multiplicity accepted")
    [[0;1;2;3]; [0;1;2;3;3]; [0;1;2;3;5]; [0;1;2;3;4;4]];
  require (Checker.check_independent_indices [0;1;0] [0;0;1]) "duplicate actions mishandled";
  require (not (Checker.check_independent_indices [0;1;0] [0;1;1])) "duplicate action dropped";
  require (Checker.check_no_commutations [0;1;0] [0;1;0]) "identity rejected";
  require (not (Checker.check_no_commutations [0;1;0] [0;0;1])) "dependent duplicate reorder accepted";
  require (Checker.check_independent_indices [] []) "empty identity rejected";
  Printf.printf "Verified extracted schedule checker: %d permutations, dependency refusal and multiplicities passed\\n"
    (List.length orders)
""")
    run("ocamlopt", "-c", "Checker.mli")
    run("ocamlopt", "-c", "Checker.ml")
    run("ocamlopt", "Checker.cmx", "Main.ml", "-o", "checker-demo")
    output = run(WORK / "checker-demo").stdout
    (WORK / "report.json").write_text(json.dumps({
        "implementation": "actual Rocq extraction of AbstractScheduleChecker.check_schedule",
        "permutations_checked": 120, "independence_refusals_checked": True,
        "missing_extra_and_duplicated_actions_checked": True,
        "proof_endpoint": "AbstractScheduleChecker.check_schedule_preserves",
        "concrete_memory_endpoint": "CompCertIndexSchedule.checked_index_schedule_preserves_actual_memory",
        "external_optimizer_called": False,
    }, indent=2) + "\n")
    print(output, end="")


if __name__ == "__main__":
    main()
