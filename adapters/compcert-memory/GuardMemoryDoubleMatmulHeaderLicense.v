From Stdlib Require Import ZArith.
From compcert.lib Require Import Maps Integers.
From compcert.common Require Import AST Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleMatmulLoops GuardMemoryDoubleNestControl GuardMemoryLongHeaderLicense.
Set Implicit Arguments.
Local Open Scope Z_scope.

(** A license is conditional on source reachability.  No value is required for
    an unreached child header, and no numeric range is established here. *)
Definition double_matmul_headers_licensed m_block n_block k_block memory : Prop :=
  exists m_word, Mem.load Mint64 memory m_block 0 = Some (Vlong m_word) /\
    (0 < Int64.signed m_word ->
      exists n_word, Mem.load Mint64 memory n_block 0 = Some (Vlong n_word) /\
        (0 < Int64.signed n_word ->
          exists k_word, Mem.load Mint64 memory k_block 0 = Some (Vlong k_word))).

Theorem double_matmul_source_headers_licensed fe ge locals temps memory site
  m_bound n_bound k_bound m_block n_block k_block after final :
  double_global_binding ge locals m_bound m_block ->
  double_global_binding ge locals n_bound n_block ->
  double_global_binding ge locals k_bound k_block ->
  exec_stmt fe ge locals temps memory (double_matmul_source_nest site m_bound n_bound k_bound)
    E0 after final Out_normal ->
  double_matmul_headers_licensed m_block n_block k_block memory.
Proof.
  intros MB NB KB RUN.
  destruct (@memory_global_long_initialized_license fe ge locals temps memory (matmul_i site)
    m_bound m_block (double_matmul_middle_source site n_bound k_bound) after final
    MB (double_matmul_middle_normal site n_bound k_bound) RUN) as [m_word [MLOAD MCHILD]].
  exists m_word; split; [exact MLOAD|intro MPOS].
  destruct (MCHILD MPOS) as [n_temps [n_memory NRUN]].
  destruct (@memory_global_long_initialized_license fe ge locals
    (PTree.set (matmul_i site) (Vlong Int64.zero) temps) memory (matmul_j site)
    n_bound n_block (double_matmul_inner_source site k_bound) n_temps n_memory
    NB (double_matmul_inner_normal site k_bound) NRUN) as [n_word [NLOAD NCHILD]].
  exists n_word; split; [exact NLOAD|intro NPOS].
  destruct (NCHILD NPOS) as [k_temps [k_memory KRUN]].
  destruct (@memory_global_long_initialized_license fe ge locals
    (PTree.set (matmul_j site) (Vlong Int64.zero)
      (PTree.set (matmul_i site) (Vlong Int64.zero) temps)) memory (matmul_k site)
    k_bound k_block (double_matmul_body site) k_temps k_memory KB eq_refl KRUN)
    as [k_word [KLOAD _]].
  exists k_word; exact KLOAD.
Qed.

Print Assumptions double_matmul_source_headers_licensed.
