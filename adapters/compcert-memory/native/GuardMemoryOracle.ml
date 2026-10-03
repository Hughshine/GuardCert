(* Untrusted Fourier-Motzkin search. The extracted VPL LCF constructs and
   checks every returned certificate; an unsuccessful search returns None. *)
open CstrLCF

module Variables = Map.Make (Z)

type t = unit

exception Search_limit

let integer_limit name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some raw -> max 0 (min 1000000 (int_of_string raw))

let row_limit = integer_limit "GUARDCERT_FM_ROWS" 4000
let operation_limit = integer_limit "GUARDCERT_FM_OPERATIONS" 100000
let searches = ref 0
let contradictions = ref 0
let exhausted = ref 0

let rational q = Q.make (GuardMemoryNumbers.export_integer q.QArith_base.coq_Qnum)
  (GuardMemoryNumbers.export_positive q.QArith_base.coq_Qden)
let checked_rational q =
  Qcanon.coq_Q2Qc { QArith_base.coq_Qnum = GuardMemoryNumbers.import_integer (Q.num q);
                  coq_Qden = GuardMemoryNumbers.import_positive (Q.den q) }

type 'c row = {
  coefficients : Q.t Variables.t;
  bound : Q.t;
  strict : bool;
  certificate : 'c Lazy.t;
}

let coefficient variable row =
  match Variables.find_opt variable row.coefficients with None -> Q.zero | Some q -> q

let scale lcf factor row = {
  coefficients = Variables.map (Q.mul factor) row.coefficients;
  bound = Q.mul factor row.bound;
  strict = row.strict;
  certificate = lazy (lcf.mul (checked_rational factor) (Lazy.force row.certificate));
}

let combine lcf first second = {
  coefficients = Variables.merge (fun _ a b ->
    let sum = Q.add (Option.value a ~default:Q.zero) (Option.value b ~default:Q.zero) in
    if Q.equal sum Q.zero then None else Some sum)
      first.coefficients second.coefficients;
  bound = Q.add first.bound second.bound;
  strict = first.strict || second.strict;
  certificate = lazy (lcf.add (Lazy.force first.certificate) (Lazy.force second.certificate));
}

let imported lcf certificate =
  let constraint_ = lcf.export certificate in
  let coefficients = List.fold_left (fun map (variable, value) ->
    let value = rational value in
    if Q.equal value Q.zero then map else Variables.add (GuardMemoryNumbers.export_positive variable) value map)
      Variables.empty (LinTerm.LinQ.export constraint_.CstrC.Cstr.coefs) in
  let row = { coefficients; bound = rational constraint_.CstrC.Cstr.cst;
              strict = constraint_.CstrC.Cstr.typ = NumC.LtT;
              certificate = lazy certificate } in
  match constraint_.CstrC.Cstr.typ with
  | NumC.EqT -> [row; scale lcf Q.minus_one row]
  | NumC.LeT | NumC.LtT -> [row]

let contradictory row =
  Variables.is_empty row.coefficients &&
    (Q.sign row.bound < 0 || (row.strict && Q.equal row.bound Q.zero))

let stronger first second =
  let comparison = Q.compare first.bound second.bound in
  comparison < 0 || (comparison = 0 && first.strict && not second.strict)

let compact lcf rows =
  if List.length rows > row_limit then raise Search_limit;
  let table = Hashtbl.create (List.length rows) in
  List.iter (fun row ->
    if not (Variables.is_empty row.coefficients) then begin
      let _, leading = Variables.min_binding row.coefficients in
      let normalized = scale lcf (Q.inv (Q.abs leading)) row in
      let key = Variables.bindings normalized.coefficients in
      match Hashtbl.find_opt table key with
      | Some old when not (stronger normalized old) -> ()
      | _ -> Hashtbl.replace table key normalized
    end) rows;
  Hashtbl.fold (fun _ row result -> row :: result) table []

let select_variable rows =
  let counts = List.fold_left (fun counts row ->
    Variables.fold (fun variable value counts ->
      let positive, negative = Option.value (Variables.find_opt variable counts) ~default:(0, 0) in
      Variables.add variable (if Q.sign value > 0 then (positive + 1, negative)
                              else (positive, negative + 1)) counts)
      row.coefficients counts) Variables.empty rows in
  fst (Variables.fold (fun variable (positive, negative) ((_, score) as best) ->
    let cost = positive * negative in
    if cost < score then (variable, cost) else best)
      counts (fst (Variables.min_binding counts), max_int))

let search input =
  let operations = ref 0 in
  let tick () = incr operations; if !operations > operation_limit then raise Search_limit in
  let rec eliminate rows =
    match List.find_opt contradictory rows with
    | Some row -> Some (Lazy.force row.certificate)
    | None ->
      let rows = compact input.lcf rows in
      if rows = [] then None else begin
        let variable = select_variable rows in
        let positive, other = List.partition (fun row -> Q.sign (coefficient variable row) > 0) rows in
        let negative, zero = List.partition (fun row -> Q.sign (coefficient variable row) < 0) other in
        if List.length positive * List.length negative + List.length zero > row_limit
        then raise Search_limit;
        let derived = List.fold_left (fun result first ->
          List.fold_left (fun result second ->
            tick ();
            let first_coefficient = coefficient variable first in
            let first = scale input.lcf (Q.neg (coefficient variable second)) first in
            let second = scale input.lcf first_coefficient second in
            combine input.lcf first second :: result) result negative) zero positive in
        eliminate derived
      end
  in
  eliminate (List.concat_map (imported input.lcf) input.cert)

let is_empty input =
  incr searches;
  let result =
    if Sys.getenv_opt "GUARDCERT_ORACLE_FAULT" = Some "top-certificate" then Some input.lcf.top
    else try search input with Search_limit -> incr exhausted; None in
  if Option.is_some result then incr contradictions;
  ImpureConfig.Core.Base.pure result

(* Keep the complete input constraints. No unproved minimization is needed;
   is_empty rebuilds its search from their checked representations. *)
let add (input, more) =
  ImpureConfig.Core.Base.pure (Some (), input.cert @ more)
