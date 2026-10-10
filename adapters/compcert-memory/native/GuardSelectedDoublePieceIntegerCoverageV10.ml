(* Untrusted normalization after affine enclosure. Retain the phase tile prefix;
   singleton point loops and exact duplicated membership tests are candidate data. *)
include GuardSelectedDoublePieceIntegerCoverageV5

let normalize_points tiles code =
  let singletons=ref 0 and memberships=ref 0 in
  let rec body depth = function
    | L.Loop (lo,hi,child) ->
        let child=body (depth+1) child in
        if depth>=tiles && is_singleton lo hi then
          (incr singletons;substitute_statement true 0 lo child)
        else
          let lower=lower_membership (shift lo) (L.Var (nat 0)) in
          let upper=upper_membership (L.Var (nat 0)) (shift hi) in
          let child=match child with
            | L.Guard (L.And (a,b),inside) when a=lower && b=upper ->
                incr memberships;inside
            | L.Guard (L.And (a,b),inside) when a=lower ->
                incr memberships;L.Guard (b,inside)
            | L.Guard (L.And (a,b),inside) when b=upper ->
                incr memberships;L.Guard (a,inside)
            | child->child in
          L.Loop (lo,hi,child)
    | L.Guard (test,child) -> L.Guard (test,body depth child)
    | L.Seq children -> L.Seq (sequence depth children)
    | code -> code
  and sequence depth = function
    | L.SNil -> L.SNil
    | L.SCons (head,tail)->L.SCons (body depth head,sequence depth tail) in
  let result=body 0 code in result,!singletons,!memberships

let adapt intervals source raw =
  match GuardSelectedDoublePieceQuotients.adapt intervals source raw with
  | Result.Err _ as refused -> refused
  | Result.Okk ((generated,context),variables) ->
      let tiles=if Sys.getenv_opt "GUARDCERT_PHASE_KIND"=Some "tiled" then 2 else 0 in
      let actual,singletons,memberships=normalize_points tiles generated in
      (match !current_path with None->() | Some path->
        emit (Filename.concat path "tree-point-cleaned-candidate.loop") (statement "" actual);
        emit (Filename.concat path "tree-point-cleaned-candidate.txt")
          (Printf.sprintf "scope=untrusted-candidate-data\nretained-tile-prefix=%d\npoint-singletons=%d\nexact-memberships=%d\nfinal-check=pending\n" tiles singletons memberships));
      Result.Okk ((actual,context),variables)
