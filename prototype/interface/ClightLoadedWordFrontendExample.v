From Stdlib Require Import List Bool.
From compcert.cfrontend Require Import Clight.
From polcert.lib Require Import ImpureAlarmConfig.
From GuardInterface Require Import ClightLoadedWordFrontendFactory ClightNestedFrontendRegion
  ClightTensorLoadedWordFactoryExample ClightTensorLoadedWordFactory ClightSignedExpressionProgress.
Import ListNotations CoreAlarmed.

Example lwf_actual_frontend_progress :
  signed_expression_region_progress_supported(ncs_frontend_source false lwf_shape)=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_indexed_frontend_progress :
  signed_expression_region_progress_supported(ncs_frontend_source true lwf_shape)=true.
Proof. vm_compute; reflexivity. Qed.
Example lwf_wrong_frontend_refused tensor_describe propose :
  check_loaded_word_frontend_region lwf_live lwf_pool(fun _ _ _=>Some(false,lwf_description))tensor_describe propose Sskip=pure None.
Proof. vm_compute; reflexivity. Qed.
Print Assumptions lwf_actual_frontend_progress.
Print Assumptions lwf_indexed_frontend_progress.
Print Assumptions lwf_wrong_frontend_refused.
