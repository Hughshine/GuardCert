(* The current-program partition is reused with the broader phase proposal.
   Existing extracted compiler theorems quantify over these arbitrary functions. *)
include GuardSelectedDoubleRectangular
let phase = GuardSelectedDoubleMixedPhaseV3.phase
let signature = GuardSelectedDoubleQuotientPartitioned.signature
let source_signature = GuardSelectedDoubleQuotientPartitioned.source_signature
let quotient_source = GuardSelectedDoubleQuotientPartitioned.quotient_source

let fallback_phase program =
  let rec collect source = match quotient_source program source with
    | Some (_,description) -> (match source_signature description with Some key -> [key] | None -> [])
    | None -> (match source with
      | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) -> collect a @ collect b
      | Clight.Slabel (_,body) -> collect body
      | Clight.Sswitch (_,cases) -> collect_cases cases
      | _ -> [])
  and collect_cases = function
    | Clight.LSnil -> []
    | Clight.LScons (_,body,rest) -> collect body @ collect_cases rest in
  let protected = List.fold_left (fun keys (_,definition) -> match definition with
    | AST.Gfun (Ctypes.Internal fn) -> keys @ collect fn.Clight.fn_body
    | _ -> keys) [] program.Ctypes.prog_defs |> List.sort_uniq String.compare in
  Printf.eprintf "GUARDCERT_QUOTIENT_PARTITION protected_models=%d\n%!" (List.length protected);
  fun before ->
    if List.mem (signature before) protected then (
      Printf.eprintf "GUARDCERT_QUOTIENT_FALLBACK_SKIP already_versioned_source=true\n%!";
      Result.Err "source model is already versioned by the quotient pass")
    else GuardSelectedDoubleMixedPhaseV3.phase before

let quotient_phase = fallback_phase
