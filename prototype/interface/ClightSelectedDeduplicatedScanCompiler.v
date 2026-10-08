(** Specialize the shared compiler proof; no host/backend proof is copied. *)
From compcert.common Require Import AST Errors Smallstep.
From compcert.cfrontend Require Import Csyntax Csem.
From compcert.x86 Require Import Asm.
From polcert.lib Require Import ImpureAlarmConfig.
From Vpl Require Import Impure.
From GuardInterface Require Import ClightDeduplicatedScanService ClightSelectedWordNestedStoreServiceCompiler.
Import CoreAlarmed.
Set Implicit Arguments.

Definition compile_selected_word_nested_store_deduplicated_regions :=
  compile_selected_word_nested_store_service_regions deduplicated_scan_builder.

Theorem compile_selected_word_nested_store_deduplicated_regions_correct
    chosen describe describe_cached propose private_count program target :
  mayReturn (compile_selected_word_nested_store_deduplicated_regions
    chosen describe describe_cached propose private_count program) (OK target) ->
  backward_simulation (Csem.semantics program) (Asm.semantics target).
Proof. apply compile_selected_word_nested_store_service_regions_correct. Qed.

Print Assumptions compile_selected_word_nested_store_deduplicated_regions_correct.
