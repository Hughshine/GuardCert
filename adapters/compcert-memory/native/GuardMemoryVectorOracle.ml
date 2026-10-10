(* Untrusted Fourier-Motzkin search with flattened linear-combination data.
   The existing extracted LCF constructs and checks the returned certificate. *)
open CstrLCF

module Variables = Map.Make (Z)
module Origins = Map.Make (Int)

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

type row = {
  coefficients : Q.t Variables.t;
  bound : Q.t;
  strict : bool;
  weights : Q.t Origins.t;
}

let coefficient variable row =
  match Variables.find_opt variable row.coefficients with None -> Q.zero | Some q -> q

let scale lcf factor row = {
  coefficients = Variables.map (Q.mul factor) row.coefficients;
  bound = Q.mul factor row.bound;
  strict = row.strict;
  weights = Origins.filter (fun _ value->not (Q.equal value Q.zero))
    (Origins.map (Q.mul factor) row.weights);
}

let combine lcf first second = {
  coefficients = Variables.merge (fun _ a b ->
    let sum = Q.add (Option.value a ~default:Q.zero) (Option.value b ~default:Q.zero) in
    if Q.equal sum Q.zero then None else Some sum)
      first.coefficients second.coefficients;
  bound = Q.add first.bound second.bound;
  strict = first.strict || second.strict;
  weights = Origins.merge (fun _ a b->
    let sum=Q.add (Option.value a ~default:Q.zero) (Option.value b ~default:Q.zero) in
    if Q.equal sum Q.zero then None else Some sum) first.weights second.weights;
}

let imported lcf ordinal certificate =
  let constraint_ = lcf.export certificate in
  let coefficients = List.fold_left (fun map (variable, value) ->
    let value = rational value in
    if Q.equal value Q.zero then map else Variables.add (GuardMemoryNumbers.export_positive variable) value map)
      Variables.empty (LinTerm.LinQ.export constraint_.CstrC.Cstr.coefs) in
  let row = { coefficients; bound = rational constraint_.CstrC.Cstr.cst;
              strict = constraint_.CstrC.Cstr.typ = NumC.LtT;
              weights = Origins.singleton ordinal Q.one } in
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

(* Opposite non-strict inequalities encode an equality. Eliminate with that
   equality first: each remaining row needs one positive linear combination,
   rather than the full positive-by-negative Fourier-Motzkin product. Every
   combination still carries the certificate checked by the extracted LCF. *)
let equality_pivot rows =
  let table = Hashtbl.create (List.length rows) in
  let counts = List.fold_left (fun counts row ->
    Variables.fold (fun variable _ counts ->
      Variables.add variable (1 + Option.value (Variables.find_opt variable counts)
        ~default:0) counts) row.coefficients counts) Variables.empty rows in
  List.iter (fun row ->
    if not row.strict then Hashtbl.replace table
      (Variables.bindings row.coefficients) row) rows;
  List.fold_left (fun best row ->
    if row.strict then best else
    let opposite = Variables.bindings (Variables.map Q.neg row.coefficients) in
    match Hashtbl.find_opt table opposite with
    | Some other when Q.equal row.bound (Q.neg other.bound) ->
      Variables.fold (fun variable value best ->
        let score = Variables.find variable counts in
        match best with
        | Some (_, _, _, old_score) when old_score >= score -> best
        | _ ->
          let positive, negative =
            if Q.sign value > 0 then row, other else other, row in
          Some (variable, positive, negative, score)) row.coefficients best
    | _ -> best) None rows

let rebuild input weights =
  let original=Array.of_list input.cert in
  let certificates=Origins.bindings weights |> List.map (fun (index,factor)->
    input.lcf.mul (checked_rational factor) original.(index)) in
  let rec balance = function
    | []->input.lcf.top
    | [certificate]->certificate
    | certificates->
        let rec pairs = function
          | first::second::rest->input.lcf.add first second::pairs rest
          | remaining->remaining in
        balance (pairs certificates) in
  balance certificates

let search input =
  let operations = ref 0 in
  let tick () = incr operations; if !operations > operation_limit then raise Search_limit in
  let rec eliminate rows =
    match List.find_opt contradictory rows with
    | Some row -> Some (rebuild input row.weights)
    | None ->
      let rows = compact input.lcf rows in
      if rows = [] then None else begin
        let derived = match equality_pivot rows with
        | Some (variable, positive, negative, _) ->
          List.map (fun row ->
            let value = coefficient variable row in
            if Q.equal value Q.zero then row else begin
              tick ();
              let pivot = if Q.sign value > 0 then negative else positive in
              let factor = Q.abs (coefficient variable pivot) in
              combine input.lcf (scale input.lcf factor row)
                (scale input.lcf (Q.abs value) pivot)
            end) rows
        | None ->
          let variable = select_variable rows in
          let positive, other = List.partition (fun row -> Q.sign (coefficient variable row) > 0) rows in
          let negative, zero = List.partition (fun row -> Q.sign (coefficient variable row) < 0) other in
          if List.length positive * List.length negative + List.length zero > row_limit
          then raise Search_limit;
          List.fold_left (fun result first ->
            List.fold_left (fun result second ->
              tick ();
              let first_coefficient = coefficient variable first in
              let first = scale input.lcf (Q.neg (coefficient variable second)) first in
              let second = scale input.lcf first_coefficient second in
              combine input.lcf first second :: result) result negative) zero positive in
        eliminate derived
      end
  in
  eliminate (List.concat (List.mapi (imported input.lcf) input.cert))

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
