(* Untrusted constraint-list proposal. Every returned certificate is an existing
   input certificate; the extracted VPL LCF and final candidate checks remain
   authoritative. Canonical keys propose elimination of exact duplicates only. *)
include GuardMemoryOracle
let add_batches = ref 0
let removed_duplicates = ref 0

let constraint_key lcf certificate =
  let constraint_ = lcf.CstrLCF.export certificate in
  let coefficients = List.fold_left (fun map (variable, value) ->
    let variable = GuardMemoryNumbers.export_positive variable in
    let value = Q.add (rational value)
      (Option.value (Variables.find_opt variable map) ~default:Q.zero) in
    if Q.equal value Q.zero then Variables.remove variable map
    else Variables.add variable value map)
    Variables.empty (LinTerm.LinQ.export constraint_.CstrC.Cstr.coefs) in
  constraint_.CstrC.Cstr.typ, Variables.bindings coefficients,
    rational constraint_.CstrC.Cstr.cst

let add (input, more) =
  incr add_batches;
  let constraints = input.CstrLCF.cert @ more in
  let seen = Hashtbl.create (List.length constraints) in
  let retained = List.filter (fun certificate ->
    let key = constraint_key input.CstrLCF.lcf certificate in
    if Hashtbl.mem seen key then (incr removed_duplicates; false)
    else (Hashtbl.add seen key (); true)) constraints in
  if Sys.getenv_opt "GUARDCERT_PHASE_TRACE" = Some "1" then
    Printf.eprintf "GUARDCERT_ORACLE_ADD batch=%d input=%d retained=%d removed_total=%d\n%!"
      !add_batches (List.length constraints) (List.length retained) !removed_duplicates;
  ImpureConfig.Core.Base.pure (Some (), retained)
