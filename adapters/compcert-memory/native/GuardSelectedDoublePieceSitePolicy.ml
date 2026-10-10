(* Site selection is untrusted data computed on the actual current program.
   Subsequent passes retain their own proved contracts for every selected site. *)
let rec without_skip = function
  | Clight.Ssequence (Clight.Sskip,body)
  | Clight.Ssequence (body,Clight.Sskip) -> without_skip body
  | body -> body

let remaining chosen program =
  let rec labels = function
    | Clight.Slabel (label,body) ->
        let protected=match GuardSelectedDoubleTreePolicies.whole_tree_source program (without_skip body) with
          | Some _->[label] | None->[] in
        protected @ labels body
    | Clight.Ssequence (a,b) | Clight.Sloop (a,b) | Clight.Sifthenelse (_,a,b) -> labels a @ labels b
    | Clight.Sswitch (_,cases) -> cases_labels cases
    | _ -> []
  and cases_labels = function
    | Clight.LSnil -> []
    | Clight.LScons (_,body,rest) -> labels body @ cases_labels rest in
  let protected=List.concat_map (fun (_,definition)->match definition with
    | AST.Gfun (Ctypes.Internal fn)->labels fn.Clight.fn_body | _->[]) program.Ctypes.prog_defs in
  let result=List.filter (fun label->not (List.mem label protected)) chosen in
  Printf.eprintf "GUARDCERT_PIECE_REMAINING chosen=%d protected=%d remaining=%d\n%!"
    (List.length chosen) (List.length chosen-List.length result) (List.length result);
  result
