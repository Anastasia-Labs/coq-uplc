From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Uplc.Builtins.
                     Import ExpectedArgNotations.
From CoqUplc Require Import Uplc.CekMachine.
From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Local Open Scope expectedArgs_scope.

Definition integer_subtraction : program := 
  (Program (Version 1 1 0)
    (Apply (Apply (Builtin SubtractInteger) (Const (Integer 55%Z))) (Const (Integer 11%Z)))
  ).

Theorem example1_correctly_interpreted : cek_execute_program integer_subtraction nil 10 = (Halt (VCon (Integer 44)), []).
Proof.
  compute.
  reflexivity.
Qed.

Definition integer_abs : program :=
  (Program (Version 1 1 0)
    (Lam "n"
      (Apply
        (Apply
          (Apply
            (Force (Builtin IfThenElse))
              (Apply (Apply (Builtin LessThanInteger) (Var "n")) (Const (Integer 0)))
          )
          (Apply (Apply (Builtin SubtractInteger) (Const (Integer 0))) (Var "n"))
        )
        (Var "n")
      )
    )
  ).

Theorem example2_correctly_interpreted : cek_execute_program integer_abs [Const (Integer 5)] 37 = (Halt (VCon (Integer 5)), []).
Proof.
  compute.
  reflexivity.
Qed.

Theorem example2_correct : forall (i : Z), cek_execute_program integer_abs [Const (Integer i)] 37 = (Halt (VCon (Integer (Z.abs i))), []).
Proof.
  intros i.
  induction i; compute; reflexivity.
Qed.

Definition integer_abs_lazy : program :=
  (Program (Version 1 1 0)
    (Lam "n"
      (Apply
        (Apply
          (Apply
            (Apply
              (Force (Builtin IfThenElse))
                (Apply (Apply (Builtin LessThanInteger) (Var "n")) (Const (Integer 0)))
            )
            (Lam "unit" (Apply (Apply (Builtin SubtractInteger) (Const (Integer 0))) (Var "n")))
          )
          (Lam "unit" (Var "n"))
        )
        (Const (Unit))
      )
    )
  ).

Theorem example3_correctly_interpreted : cek_execute_program integer_abs_lazy [Const (Integer 5)] 34 = (Halt (VCon (Integer 5)), []).
Proof. 
  compute.
  reflexivity.
Qed.

Theorem example3_correct : forall (i : Z), cek_execute_program integer_abs_lazy [Const (Integer i)] 42 = (Halt (VCon (Integer (Z.abs i))), []).
Proof.
  intros i.
  induction i; compute; reflexivity.
Qed.

Definition integer_abs_lazy_delays : program :=
  (Program (Version 1 1 0)
    (Lam "n"
      (Force
        (Apply
          (Apply
            (Apply
              (Force (Builtin IfThenElse))
                (Apply (Apply (Builtin LessThanInteger) (Var "n")) (Const (Integer 0)))
            )
            (Delay (Apply (Apply (Builtin SubtractInteger) (Const (Integer 0))) (Var "n")))
          )
          (Delay (Var "n"))
        )
      )
    )
  ).

Theorem example3_4_equivalence : forall (i : Z), cek_execute_program integer_abs_lazy_delays [Const (Integer i)] 42 =
                                                 cek_execute_program integer_abs_lazy        [Const (Integer i)] 42.
Proof.
  intros i.
  induction i; compute; reflexivity.
Qed.
