From Stdlib Require Import List String ZArith.
From compcert.lib Require Import Coqlib Integers Floats.
From compcert.common Require Import AST.
From compcert.cfrontend Require Import Ctypes Cop Clight.
From compcert.export Require Import Clightdefs.
From GuardOriginalMatmul Require Import OriginalMatmul.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope clight_scope.
Definition raw_original_matmul_region : statement :=
(Ssequence
  (Ssequence Sskip (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tlong)))
  (Sloop
    (Ssequence
      (Ssequence
        Sskip
        (Sifthenelse (Ebinop Olt (Etempvar _i tlong) (Evar _M tlong) tint)
          Sskip
          Sbreak))
      (Ssequence
        (Ssequence
          Sskip
          (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tlong)))
        (Sloop
          (Ssequence
            (Ssequence
              Sskip
              (Sifthenelse (Ebinop Olt (Etempvar _j tlong) (Evar _N tlong)
                             tint)
                Sskip
                Sbreak))
            (Ssequence
              (Ssequence
                Sskip
                (Sset _k__1 (Ecast (Econst_int (Int.repr 0) tint) tlong)))
              (Sloop
                (Ssequence
                  (Ssequence
                    Sskip
                    (Sifthenelse (Ebinop Olt (Etempvar _k__1 tlong)
                                   (Evar _K tlong) tint)
                      Sskip
                      Sbreak))
                  (Ssequence
                    Sskip
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Ederef
                            (Ebinop Oadd
                              (Evar _C (tarray (tarray tdouble 100) 100))
                              (Ebinop Oadd (Etempvar _i tlong)
                                (Econst_int (Int.repr 2) tint) tlong)
                              (tptr (tarray tdouble 100)))
                            (tarray tdouble 100))
                          (Ebinop Oadd (Etempvar _j tlong)
                            (Econst_int (Int.repr 2) tint) tlong)
                          (tptr tdouble)) tdouble)
                      (Ebinop Oadd
                        (Ebinop Omul (Evar _beta tdouble)
                          (Ederef
                            (Ebinop Oadd
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _C (tarray (tarray tdouble 100) 100))
                                  (Ebinop Oadd (Etempvar _i tlong)
                                    (Econst_int (Int.repr 2) tint) tlong)
                                  (tptr (tarray tdouble 100)))
                                (tarray tdouble 100))
                              (Ebinop Oadd (Etempvar _j tlong)
                                (Econst_int (Int.repr 2) tint) tlong)
                              (tptr tdouble)) tdouble) tdouble)
                        (Ebinop Omul
                          (Ebinop Omul (Evar _alpha tdouble)
                            (Ederef
                              (Ebinop Oadd
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _A (tarray (tarray tdouble 100) 100))
                                    (Ebinop Oadd (Etempvar _i tlong)
                                      (Econst_int (Int.repr 2) tint) tlong)
                                    (tptr (tarray tdouble 100)))
                                  (tarray tdouble 100))
                                (Ebinop Oadd (Etempvar _k__1 tlong)
                                  (Econst_int (Int.repr 2) tint) tlong)
                                (tptr tdouble)) tdouble) tdouble)
                          (Ederef
                            (Ebinop Oadd
                              (Ederef
                                (Ebinop Oadd
                                  (Evar _B (tarray (tarray tdouble 100) 100))
                                  (Ebinop Oadd (Etempvar _k__1 tlong)
                                    (Econst_int (Int.repr 2) tint) tlong)
                                  (tptr (tarray tdouble 100)))
                                (tarray tdouble 100))
                              (Ebinop Oadd (Etempvar _j tlong)
                                (Econst_int (Int.repr 2) tint) tlong)
                              (tptr tdouble)) tdouble) tdouble) tdouble))))
                (Ssequence
                  Sskip
                  (Sset _k__1
                    (Ebinop Oadd (Etempvar _k__1 tlong)
                      (Econst_int (Int.repr 1) tint) tlong))))))
          (Ssequence
            Sskip
            (Sset _j
              (Ebinop Oadd (Etempvar _j tlong) (Econst_int (Int.repr 1) tint)
                tlong))))))
    (Ssequence
      Sskip
      (Sset _i
        (Ebinop Oadd (Etempvar _i tlong) (Econst_int (Int.repr 1) tint)
          tlong))))).

From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryLongControl GuardMemoryLongProgressControl
  GuardMemoryDoubleMatmul.
From GuardOriginalMatmul Require Import OriginalMatmulBody.
Definition raw_original_long_loop iterator bound body :=
  Ssequence (Ssequence Sskip (Sset iterator memory_long_zero))
    (Sloop (Ssequence (Ssequence Sskip
      (Sifthenelse (long_counter_condition iterator (Evar bound memory_long_type)) Sskip Sbreak)) body)
      (Ssequence Sskip (long_counter_increment iterator))).
Lemma original_matmul_raw_frontend_shape : raw_original_matmul_region =
  raw_original_long_loop _i _M (raw_original_long_loop _j _N
    (raw_original_long_loop _k__1 _K (Ssequence Sskip (double_matmul_body original_matmul_site)))).
Proof. reflexivity. Qed.
Print Assumptions original_matmul_raw_frontend_shape.
