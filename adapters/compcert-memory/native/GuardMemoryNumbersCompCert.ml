(* The CompCert driver retains structural Rocq integers. These conversions
   belong to the untrusted certificate search; the LCF checks its output. *)
let rec export_positive = function
  | BinNums.Coq_xH -> Z.one
  | BinNums.Coq_xO rest -> Z.shift_left (export_positive rest) 1
  | BinNums.Coq_xI rest -> Z.succ (Z.shift_left (export_positive rest) 1)

let export_integer = function
  | BinNums.Z0 -> Z.zero
  | BinNums.Zpos value -> export_positive value
  | BinNums.Zneg value -> Z.neg (export_positive value)

let rec import_positive value =
  if Z.sign value <= 0 then invalid_arg "positive certificate denominator"
  else if Z.equal value Z.one then BinNums.Coq_xH
  else
    let rest = import_positive (Z.shift_right value 1) in
    if Z.testbit value 0 then BinNums.Coq_xI rest else BinNums.Coq_xO rest

let import_integer value =
  match Z.sign value with
  | 0 -> BinNums.Z0
  | 1 -> BinNums.Zpos (import_positive value)
  | _ -> BinNums.Zneg (import_positive (Z.neg value))
