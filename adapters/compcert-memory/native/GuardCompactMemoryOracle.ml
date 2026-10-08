(* Ordinary constraint compaction above the existing checked LCF oracle.
   This is not an equivalence certificate. ExactCs.fromCs checks every original
   constraint after building the proposed representation; a failed check makes
   canonize_Cs retain the original polyhedron. Other abstract-domain users keep
   their existing one-way/checked contracts. *)
include GuardMemoryOracle
open CstrLCF

let compactions = ref 0
let supplied_rows = ref 0
let retained_rows = ref 0
let peak_supplied_rows = ref 0

let compact_certificates lcf certificates =
  if List.length certificates>row_limit then raise Search_limit;
  let rows=List.concat_map(imported lcf)certificates in
  match List.find_opt contradictory rows with
  | Some row -> [Lazy.force row.certificate]
  | None ->
    let table=Hashtbl.create(List.length rows) in
    List.iter(fun row ->
      if not(Variables.is_empty row.coefficients) then begin
        let _,leading=Variables.min_binding row.coefficients in
        let factor=Q.inv(Q.abs leading) in
        let normalized={row with
          coefficients=Variables.map(Q.mul factor)row.coefficients;
          bound=Q.mul factor row.bound} in
        let key=Variables.bindings normalized.coefficients in
        match Hashtbl.find_opt table key with
        | Some(old,_) when not(stronger normalized old) -> ()
        | _ -> Hashtbl.replace table key (normalized,row)
      end)rows;
    (* Use the original checked certificate, keeping its integral representation.
       Sorting stabilizes the proposal and later bounded search order. *)
    Hashtbl.fold(fun key (_,row) result -> (key,row)::result)table []
    |> List.sort(fun (a,_) (b,_) -> Stdlib.compare a b)
    |> List.map(fun (_,row) -> Lazy.force row.certificate)

let add (input,more) =
  let original=input.cert @ more in
  let retained=if Sys.getenv_opt "GUARDCERT_CANONICALIZE"=Some "disabled" then original
    else try compact_certificates input.lcf original with Search_limit -> original in
  incr compactions;
  supplied_rows:= !supplied_rows+List.length original;
  retained_rows:= !retained_rows+List.length retained;
  peak_supplied_rows:=max !peak_supplied_rows(List.length original);
  ImpureConfig.Core.Base.pure(Some (),retained)

let () = at_exit(fun () ->
  match Sys.getenv_opt "GUARDCERT_CANONICAL_DIAGNOSTICS" with
  | None -> ()
  | Some path ->
    let channel=open_out path in
    Fun.protect ~finally:(fun () -> close_out channel)(fun () ->
      Printf.fprintf channel
        "compactions=%d\nsupplied-rows=%d\nretained-rows=%d\npeak-supplied-rows=%d\nsearches=%d\ncontradictions=%d\nexhausted=%d\n"
        !compactions !supplied_rows !retained_rows !peak_supplied_rows
        !searches !contradictions !exhausted))
