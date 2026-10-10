(* Untrusted whole-tree bounds and coordinate proposals. The extracted factory
   validates the actual final Loop, arithmetic, private names and source model. *)
include GuardSelectedDoubleVerifiedPrefixCoordinates
module Tree = GuardMemoryDoubleSourceTreeData
module Decode = GuardMemoryDoubleSourceTreeDecode
module Capture = GuardMemoryDoubleTreeCapturePrepared
module Exit = GuardMemoryDoubleTreeExitCode
module Factory = DoubleTreeRegionFactory

let profile key fallback = match Sys.getenv_opt key with
  | None -> integer (Z.of_int fallback)
  | Some text -> integer (Z.of_string text)
let lower_proposal _ _ = profile "GUARDCERT_TREE_LOWER" 0
let upper_proposal _ _ = profile "GUARDCERT_TREE_UPPER" 4096

let enclosing_bounds intervals code =
  let proposals = ref [] in
  let rec adapt depth bounds = function
    | L.Loop (lower,upper,body) ->
      let affine expression = Option.is_some (linear expression) in
      let lo,hi,reason =
        if affine lower && affine upper then lower,upper,"affine-bounds-retained"
        else match paired_bounds lower upper with
        | Some (lo,hi,width) -> lo,hi,"local-affine-width=" ^ Z.to_string width
        | None ->
          let lo = match interval bounds lower with
            | Some (value,_) -> L.Constant (integer value)
            | None -> invalid_arg "whole-tree lower interval unavailable" in
          let hi = match interval bounds upper with
            | Some (_,value) -> L.Constant (integer value)
            | None -> invalid_arg "whole-tree upper interval unavailable" in
          lo,hi,"captured-interval-enclosure" in
      proposals := (Printf.sprintf "depth=%d %s lower=%s upper=%s" depth reason
        (loop_expression lo) (loop_expression hi)) :: !proposals;
      let next = match interval bounds lo,interval bounds hi with
        | Some (lo,_),Some (_,hi) -> Some (lo,maximum lo hi)
        | _ -> None in
      let body = adapt (depth+1) (next::bounds) body in
      let body = L.Guard (L.And (lower_membership (shift lower) (L.Var (nat 0)),
        upper_membership (L.Var (nat 0)) (shift upper)),body) in
      L.Loop (lo,hi,body)
    | L.Guard (test,body) -> L.Guard (test,adapt depth bounds body)
    | L.Instr _ as point -> point
    | L.Seq sequence -> L.Seq (adapt_sequence depth bounds sequence)
  and adapt_sequence depth bounds = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail) -> L.SCons (adapt depth bounds head,adapt_sequence depth bounds tail) in
  let bounds = List.map (fun (lower,upper) -> Some
    (GuardMemoryNumbers.export_integer lower,GuardMemoryNumbers.export_integer upper)) intervals in
  let result = adapt 0 bounds code in
  result,String.concat "\n" (List.rev !proposals) ^ "\n"

let adapt intervals ((raw,context),variables) =
  incr adaptations;
  verified_predicates := 0; cleared_floor_nodes := 0;
  try
    if List.length context <> List.length intervals then
      invalid_arg "whole-tree parameter interval layout differs from codegen context";
    let path = match !current_path with Some path -> path | None -> failwith "missing phase receipt" in
    emit (Filename.concat path "tree-raw-generated.loop") (statement "" raw);
    let without_singletons,singletons = singleton_eliminate raw in
    let recovered,translations = recover_points without_singletons in
    emit (Filename.concat path "tree-point-normalized.loop") (statement "" recovered);
    let generated,proposals = enclosing_bounds intervals recovered in
    let generated,moved = hoist_independent generated in
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d hoisted=%d predicates=%d floor-nodes=%d\nfinal-check=pending\n"
        singletons translations moved !verified_predicates !cleared_floor_nodes);
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)

let whole_tree_source program = function
  | Clight.Ssequence (capture,Clight.Sifthenelse (Clight.Etempvar (flag,_),
      Clight.Ssequence (_,restore),fallback)) ->
    (match Decode.checked_double_source_tree program fallback with
    | None -> None
    | Some tree ->
      let caches = GuardSelectedDoubleCandidate.assigned_temps capture
        |> List.filter (fun key -> key<>flag)
        |> List.fold_left (fun keys key -> if List.mem key keys then keys else keys@[key]) [] in
      let cache = Factory.double_tree_allocated_cache tree caches flag in
      if capture=Capture.double_tree_capture_prepare tree cache flag (lower_proposal tree) (upper_proposal tree)
        && restore=Exit.double_tree_exit_code tree cache then Some tree else None)
  | _ -> None

let rec installed program source = match whole_tree_source program source with
  | Some _ -> 1
  | None -> (match source with
    | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) -> installed program a + installed program b
    | Clight.Slabel (_,body) -> installed program body
    | Clight.Sswitch (_,cases) -> installed_cases program cases
    | _ -> 0)
and installed_cases program = function
  | Clight.LSnil -> 0
  | Clight.LScons (_,body,rest) -> installed program body + installed_cases program rest

let trace_clight program =
  let regions = List.fold_left (fun count (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> count + installed program fn.Clight.fn_body
    | _ -> count) 0 program.Ctypes.prog_defs in
  Printf.eprintf "GUARDCERT_TREE_INSTALLED regions=%d phase_calls=%d adaptations=%d\n%!"
    regions !calls !adaptations
