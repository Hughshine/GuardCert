(* Untrusted tiling proposal over a source-filtered finite box. *)
module L = GuardMemoryLoops.L
let nat = GuardMemoryCandidate.natural
let rec size = function Datatypes.O -> 0 | Datatypes.S rest -> 1 + size rest
let number value = GuardMemoryNumbers.import_integer (Z.of_int value)

let rec shift_expression depth = function
  | L.Var index -> let position = size index in
      L.Var (nat (if position < depth then position else position + 2))
  | L.Sum (a,b) -> L.Sum (shift_expression depth a,shift_expression depth b)
  | L.Mult (factor,a) -> L.Mult (factor,shift_expression depth a)
  | L.Div (a,divisor) -> L.Div (shift_expression depth a,divisor)
  | L.Mod (a,divisor) -> L.Mod (shift_expression depth a,divisor)
  | L.Min (a,b) -> L.Min (shift_expression depth a,shift_expression depth b)
  | L.Max (a,b) -> L.Max (shift_expression depth a,shift_expression depth b)
  | constant -> constant
let rec shift_test depth = function
  | L.LE (a,b) -> L.LE (shift_expression depth a,shift_expression depth b)
  | L.EQ (a,b) -> L.EQ (shift_expression depth a,shift_expression depth b)
  | L.And (a,b) -> L.And (shift_test depth a,shift_test depth b)
  | L.Or (a,b) -> L.Or (shift_test depth a,shift_test depth b)
  | L.Not a -> L.Not (shift_test depth a)
  | constant -> constant
let rec shift_statement depth = function
  | L.Loop (lower,upper,body) -> L.Loop (shift_expression depth lower,
      shift_expression depth upper,shift_statement (depth+1) body)
  | L.Guard (test,body) -> L.Guard (shift_test depth test,shift_statement depth body)
  | L.Instr (instruction,arguments) -> L.Instr (instruction,List.map (shift_expression depth) arguments)
  | L.Seq statements -> L.Seq (shift_sequence depth statements)
and shift_sequence depth = function
  | L.SNil -> L.SNil
  | L.SCons (first,rest) -> L.SCons (shift_statement depth first,shift_sequence depth rest)
let rec instruction_count = function
  | L.Instr _ -> 1
  | L.Loop (_,_,body) | L.Guard (_,body) -> instruction_count body
  | L.Seq statements -> sequence_count statements
and sequence_count = function
  | L.SNil -> 0
  | L.SCons (first,rest) -> instruction_count first + sequence_count rest

let propose request boxed rows columns =
  if rows <= 0 || columns <= 0 || rows > 1024 || columns > 1024 then
    invalid_arg "affine tile policy width";
  let axes = request.AffineNestCheckedCompiler.affine_requested_axes in
  let dimensions = List.length axes in
  let rows,columns = number rows,number columns in
  let tile_bounds (lower,upper) width =
    let lower = GuardMemoryNumbers.export_integer lower in
    let upper = GuardMemoryNumbers.export_integer upper in
    let width = GuardMemoryNumbers.export_integer width in
    L.Constant (GuardMemoryNumbers.import_integer (Z.ediv lower width)),
    L.Constant (GuardMemoryNumbers.import_integer (Z.succ (Z.ediv (Z.pred upper) width))) in
  let inside axis coordinate =
    let lower,upper = List.nth axes axis in
    L.And (L.LE (L.Constant lower,coordinate),
           L.LE (coordinate,L.Sum (L.Constant upper,L.Constant (number (-1))))) in
  let point_loop width tile body = L.Loop (L.Mult (width,tile),
      L.Sum (L.Mult (width,tile),L.Constant width),body) in
  match boxed with
  | L.Loop (_,_,L.Loop (_,_,body)) ->
      let body = L.Guard (L.And (inside 0 (L.Var (nat 1)),inside 1 (L.Var (nat 0))),
                         shift_statement 2 body) in
      let points = point_loop rows (L.Var (nat 1))
        (point_loop columns (L.Var (nat 1)) body) in
      let low_j,high_j = tile_bounds (List.nth axes 1) columns in
      let low_i,high_i = tile_bounds (List.nth axes 0) rows in
      let candidate = L.Loop (low_i,high_i,L.Loop (low_j,high_j,points)) in
      let witness = GuardMemoryScalarTiling.memory_scalar_tiling_witness (nat dimensions)
        (nat (List.length request.AffineNestCheckedCompiler.affine_requested_context)) rows columns in
      candidate,List.init (instruction_count boxed) (fun _ -> witness)
  | _ -> invalid_arg "affine tiling requires two axes"
