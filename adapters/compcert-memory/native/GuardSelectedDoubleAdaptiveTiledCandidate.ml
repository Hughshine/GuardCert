(* Resource and representation proposals from the actual Csyntax input.
   The existing extracted factories check freshness, capacity and every witness.
   This estimate is neither a proved minimum nor a guarantee for every phase. *)
include GuardSelectedDoubleReindexedTiledCandidate

let source_depth = ref 0
let proposed_private_count = ref 16
let proposed_witness_axes = ref 6

let rec loop_depth = function
  | Csyntax.Swhile (_, body) | Csyntax.Sdowhile (_, body) -> 1 + loop_depth body
  | Csyntax.Sfor (initial, _, step, body) ->
    max (loop_depth initial) (max (loop_depth step) (1 + loop_depth body))
  | Csyntax.Ssequence (first, second) | Csyntax.Sifthenelse (_, first, second) ->
    max (loop_depth first) (loop_depth second)
  | Csyntax.Slabel (_, body) -> loop_depth body
  | Csyntax.Sswitch (_, cases) -> cases_depth cases
  | _ -> 0
and cases_depth = function
  | Csyntax.LSnil -> 0
  | Csyntax.LScons (_, body, rest) -> max (loop_depth body) (cases_depth rest)

let configure program =
  source_depth := List.fold_left (fun depth (_, definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> max depth (loop_depth fn.Csyntax.fn_body)
    | _ -> depth) 0 program.Ctypes.prog_defs;
  let candidate_depth = (if enabled () then 2 else 1) * !source_depth in
  proposed_private_count := max 16 (2 * candidate_depth + 2);
  proposed_witness_axes := max 6 candidate_depth;
  let private_count = match Sys.getenv_opt "GUARDCERT_DOUBLE_PRIVATE_COUNT" with
    | None -> !proposed_private_count | Some text -> int_of_string text in
  let axes = match Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES" with
    | None -> !proposed_witness_axes | Some text -> int_of_string text in
  if private_count < 0 then invalid_arg "private count must be nonnegative";
  if axes < 0 then invalid_arg "witness axes must be nonnegative";
  Printf.eprintf
    "GUARDCERT_DOUBLE_POLICY source_loop_depth=%d private_count=%d witness_axes=%d private_override=%b witness_override=%b\n%!"
    !source_depth private_count axes
    (Option.is_some (Sys.getenv_opt "GUARDCERT_DOUBLE_PRIVATE_COUNT"))
    (Option.is_some (Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES"))

let private_count () =
  let count = match Sys.getenv_opt "GUARDCERT_DOUBLE_PRIVATE_COUNT" with
    | None -> !proposed_private_count | Some text -> int_of_string text in
  if count < 0 then invalid_arg "private count must be nonnegative";
  nat count

let choices () =
  let axes = match Sys.getenv_opt "GUARDCERT_DOUBLE_WITNESS_AXES" with
    | None -> !proposed_witness_axes | Some text -> int_of_string text in
  if axes < 0 then invalid_arg "witness axes must be nonnegative";
  if enabled () || GuardSelectedDoubleCandidate.mode () = "affine" then
    [] :: List.init (max 0 (axes - 1)) (fun axis -> [nat axis])
  else [[]]
