(* Untrusted numerical proposals for the shifted final checker. Coalescing may
   discard proposal guards; the checker must establish every resulting domain
   and dependence obligation before the factory can install the actual code. *)
include GuardSelectedDoubleTreePolicies

(* This is an untrusted shape proposal. It may erase outer guards; the
   actual extracted domain/dependence checker remains the acceptance authority. *)
let rec flattened = function
  | L.Seq sequence -> flattened_sequence sequence
  | code -> [code]
and flattened_sequence = function
  | L.SNil -> []
  | L.SCons (head,tail) -> flattened head @ flattened_sequence tail
let sequence nodes = L.Seq (List.fold_right (fun head tail -> L.SCons (head,tail)) nodes L.SNil)
let is_point = function L.Instr _ -> true | _ -> false
let prefix first second =
  let rec go = function
    | [],_ -> true
    | head::tail,other::rest when head=other -> go (tail,rest)
    | _ -> false in
  go (first,second)
let coalesce_prefix code =
  let piece = function
    | L.Guard (_,L.Loop (lo,hi,body)) -> Some (lo,hi,flattened body)
    | L.Loop (lo,hi,body) -> Some (lo,hi,flattened body)
    | _ -> None in
  let pieces = List.map piece (flattened code) in
  if List.length pieces < 2 || List.exists Option.is_none pieces then code,0 else
  let pieces = List.map Option.get pieces in
  let lo,_,_ = List.hd pieces in
  let _,finish,points = List.hd (List.rev pieces) in
  let rec compatible = function
    | [] -> false
    | [(_,hi,body)] -> hi=finish && body=points
    | (_,hi,body)::((next,_,next_body)::_ as tail) ->
      hi=L.Min (next,finish) && prefix body next_body && List.length body < List.length next_body && compatible tail in
  if not (List.for_all is_point points && compatible pieces) then code,0 else
  let rec introduce previous = function
    | [] -> []
    | (start,_,body)::rest ->
      let added = List.filteri (fun index _ -> index>=previous) body in
      List.map (fun point -> if previous=0 then point else
        L.Guard (L.LE (shift start,L.Var (nat 0)),point)) added @
      introduce (List.length body) rest in
  sequence [L.Loop (lo,finish,sequence (introduce 0 pieces))],List.length pieces-1

let shift_proposal ((body,_),_) =
  let rec collect depth = function
    | L.Loop (_,_,body) -> collect (depth+1) body
    | L.Guard (_,body) -> collect depth body
    | L.Seq sequence -> collect_sequence depth sequence
    | L.Instr (_,arguments) ->
      let delta = match arguments with
        | argument::_ -> (match linear argument with
          | Some (coefficients,constant) when depth>0 &&
              Coefficients.bindings coefficients = [depth-1,Z.one] -> constant
          | _ -> Z.zero)
        | [] -> Z.zero in
      [integer (if Sys.getenv_opt "GUARDCERT_TREE_POINT_SHIFT" = Some "wrong"
        then Z.succ delta else delta)]
  and collect_sequence depth = function
    | L.SNil -> []
    | L.SCons (head,tail) -> collect depth head @ collect_sequence depth tail in
  let deltas = collect 0 body in
  (match !current_path with Some path -> emit (Filename.concat path "tree-shifts.txt")
    (String.concat "," (List.map integer_text deltas) ^ "\n") | None -> ());
  deltas

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
    let coalesced,merges = coalesce_prefix recovered in
    emit (Filename.concat path "tree-coalesced.loop") (statement "" coalesced);
    let generated,proposals = enclosing_bounds intervals coalesced in
    let generated,moved = hoist_independent generated in
    emit (Filename.concat path "tree-bounded-proposals.txt") proposals;
    emit (Filename.concat path "tree-generated.loop") (statement "" generated);
    emit (Filename.concat path "tree-normalization.txt")
      (Printf.sprintf "singletons=%d translations=%d coalesced-prefixes=%d hoisted=%d\nfinal-check=pending\n"
        singletons translations merges moved);
    Result.Okk ((generated,context),variables)
  with (Invalid_argument _ | Failure _ | Sys_error _) as error ->
    (match !current_path with Some path -> emit (Filename.concat path "tree-adaptation-refusal.txt")
      (Printexc.to_string error ^ "\n") | None -> ());
    Result.Err (Printexc.to_string error)
