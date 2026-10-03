(* This is an untrusted proposal. Extracted TopoSort.check_toposort checks
   the permutation and every prohibited ordering before it can be used. *)
let rec nat = function 0 -> Datatypes.O | n -> Datatypes.S (nat (n - 1))

let sort constraints =
  let matrix = Array.of_list (List.map Array.of_list constraints) in
  let count = Array.length matrix in
  let prohibited first second =
    second >= Array.length matrix.(first) || matrix.(first).(second)
  in
  let rec choose done_indices remaining =
    match remaining with
    | [] -> List.rev done_indices
    | _ ->
      match List.find_opt
        (fun first -> List.for_all
          (fun second -> first = second || not (prohibited first second)) remaining)
        remaining with
      | None -> []
      | Some first -> choose (nat first :: done_indices)
          (List.filter ((<>) first) remaining)
  in
  (* A resource refusal is also checked and cannot certify a permutation. *)
  let proposal = if count > 256 then [] else choose [] (List.init count Fun.id) in
  ImpureAlarmConfig.CoreAlarmed.Base.pure proposal
