(* Diagnostic data callback. Inspection never substitutes for checker results. *)
include GuardSelectedDoubleAffineTiledCandidate
module P = GuardMemoryDoublePolyhedral.DoubleAssignmentIRs.PolyLang
module C = GuardMemoryDoubleCandidateProgress.DoubleCandidate
module I = GuardMemoryDoubleExtractedTiling
let rows rows = String.concat ";" (List.map (fun (coefficients,bias) ->
  String.concat "," (List.map integer_text coefficients) ^ ":" ^ integer_text bias) rows)
let show name instructions = String.concat "\n" (List.mapi (fun index instruction ->
  name ^ string_of_int index ^ " domain=" ^ rows instruction.P.pi_poly ^
  "\ntransform=" ^ rows instruction.P.pi_transformation ^
  "\naccess-transform=" ^ rows instruction.P.pi_access_transformation ^
  "\nschedule=" ^ rows instruction.P.pi_schedule) instructions)
let rec first_instruction = function
  | L.Loop(_,_,body) | L.Guard(_,body) -> first_instruction body
  | L.Instr(instruction,_) -> Some instruction
  | L.Seq sequence -> first_sequence sequence
and first_sequence = function
  | L.SNil -> None
  | L.SCons(head,tail) -> match first_instruction head with
    | Some _ as found -> found | None -> first_sequence tail
let evaluate computation =
  let outcome = ref None in
  ImpureConfig.Core.Base.bind computation (fun (value,alarm_free) ->
    outcome := Some (value,alarm_free); ());
  match !outcome with Some (value,true) -> value | _ -> failwith "inspection alarm"
let inspect ((body,context),variables) =
  let point = match !current_witnesses with witness::_ ->
    GuardOpenScopDoubleIO.nat_to_int witness.TilingWitness.stw_point_dim
    | [] -> failwith "missing diagnostic witness" in
  let instruction = match first_instruction body with Some instruction -> instruction
    | None -> failwith "missing diagnostic instruction" in
  let rec source depth = if depth = point then L.Instr(instruction,
    List.init point (fun axis -> L.Var(nat(point-1-axis))))
    else L.Loop(L.Constant(small 0),L.Var(nat depth),source(depth+1)) in
  let extract code = match GuardMemoryDoublePolyhedral.DoubleAssignmentExtractor.extractor
    ((code,context),variables) with Result.Okk ((instructions,_),_) -> instructions
    | Result.Err _ -> failwith "diagnostic extraction refused" in
  let before = C.memory_normalized_instructions (extract (source 0)) in
  let after = extract body in
  let lines = List.map (fun swaps ->
    let normalized = C.memory_normalized_instructions
      (C.memory_reindexed_instructions (nat(List.length context)) swaps after) in
    let header = "swaps=" ^ String.concat "," (List.map(fun n ->
      string_of_int(GuardOpenScopDoubleIO.nat_to_int n)) swaps) in
    let result = match I.double_attach_tiling_instructions (nat(List.length context))
      before normalized !current_witnesses with
      | None -> "attachment=false"
      | Some tiled ->
        let reference = List.map (P.current_view_pi (nat(List.length context))) tiled in
        let alignment = evaluate (C.memory_align_domains reference normalized) in
        let check = match alignment with None -> "alignment=false" | Some aligned ->
          "alignment=true equality=" ^ string_of_bool(I.double_tiling_pinstr_list_eqb reference aligned) in
        show "reference" reference ^ "\n" ^ check in
    header ^ "\n" ^ show "candidate" normalized ^ "\n" ^ result) (choices ()) in
  match !current_path with Some directory -> emit (Filename.concat directory "final-check-inspection.txt")
    ("Diagnostic source reconstruction; not a source execution certificate.\n" ^
      show "source" before ^ "\n" ^ String.concat "\n" lines ^ "\n") | None -> ()
let adapt limit code = match GuardSelectedDoubleAffineTiledCandidate.adapt limit code with
  | Result.Err _ as result -> result
  | Result.Okk candidate as result ->
    (try inspect candidate with error ->
      match !current_path with Some directory -> emit (Filename.concat directory "inspection-error.txt")
        (Printexc.to_string error ^ "\n") | None -> ());
    result
