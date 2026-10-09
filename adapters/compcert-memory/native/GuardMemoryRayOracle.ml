(* Untrusted constraint-list proposal. Keep an existing certificate for the
   strongest normalized parallel halfspace; keep distinct equalities. The
   original LCF and ExactCs reverse-inclusion checks remain authoritative. *)
include GuardMemoryOracle

type direction =
  | Equality of (Z.t * Q.t) list * Q.t
  | Halfspace of (Z.t * Q.t) list

type 'c proposal = {
  direction : direction;
  bound : Q.t;
  strict : bool;
  certificate : 'c;
  ordinal : int;
}

let add_batches = ref 0
let removed_constraints = ref 0

let describe lcf ordinal certificate =
  let constraint_ = lcf.CstrLCF.export certificate in
  let coefficients = List.fold_left (fun map (variable, value) ->
    let variable = GuardMemoryNumbers.export_positive variable in
    let value = Q.add (rational value)
      (Option.value (Variables.find_opt variable map) ~default:Q.zero) in
    if Q.equal value Q.zero then Variables.remove variable map
    else Variables.add variable value map)
    Variables.empty (LinTerm.LinQ.export constraint_.CstrC.Cstr.coefs) in
  let typ = constraint_.CstrC.Cstr.typ in
  let scale = match Variables.min_binding_opt coefficients with
    | None -> Q.one
    | Some (_, leading) -> Q.inv (if typ = NumC.EqT then leading else Q.abs leading) in
  let normalized = Variables.bindings (Variables.map (Q.mul scale) coefficients) in
  let bound = Q.mul scale (rational constraint_.CstrC.Cstr.cst) in
  let direction = if typ = NumC.EqT then Equality (normalized, bound) else Halfspace normalized in
  { direction; bound; strict = typ = NumC.LtT; certificate; ordinal }

let stronger first second =
  let comparison = Q.compare first.bound second.bound in
  comparison < 0 || (comparison = 0 && first.strict && not second.strict)

let add (input, more) =
  incr add_batches;
  let constraints = input.CstrLCF.cert @ more in
  let proposals = List.mapi (describe input.CstrLCF.lcf) constraints in
  let winners = Hashtbl.create (List.length proposals) in
  List.iter (fun proposed ->
    match Hashtbl.find_opt winners proposed.direction with
    | Some old when not (stronger proposed old) -> ()
    | _ -> Hashtbl.replace winners proposed.direction proposed) proposals;
  let retained = List.filter_map (fun proposed ->
    let winner = Hashtbl.find winners proposed.direction in
    if winner.ordinal = proposed.ordinal then Some proposed.certificate else None) proposals in
  removed_constraints := !removed_constraints + List.length constraints - List.length retained;
  if Sys.getenv_opt "GUARDCERT_PHASE_TRACE" = Some "1" then
    Printf.eprintf "GUARDCERT_ORACLE_RAY_ADD batch=%d input=%d retained=%d removed_total=%d\n%!"
      !add_batches (List.length constraints) (List.length retained) !removed_constraints;
  ImpureConfig.Core.Base.pure (Some (), retained)
