From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.List.
From CoqUplc Require Import Prelude.Monad.
                     Import MonadNotations.
From CoqUplc Require Import Prelude.Show.
From CoqUplc Require Import Unicode.String.
From CoqUplc Require Import Unicode.StringShow.

From CoqUplc Require Import Uplc.BuiltinFunctions.Evaluate.
From CoqUplc Require Import Uplc.Builtins.
                     Import BuiltinNotations.
From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Inductive frame : Set :=
  | ForceFrame              :                                                   frame
  | LeftApplicationToTerm   : term -> environment                            -> frame
  | LeftApplicationToValue  : cekValue                                       -> frame
  | RightApplicationOfValue : cekValue                                       -> frame
  | ConstructorArgument     : N -> list cekValue -> list term -> environment -> frame
  | CaseScrutinee           :                       list term -> environment -> frame.

Notation stack := (list frame).

Inductive state : Set :=
  | Eval   : stack -> environment -> term -> state
  | Return : stack -> cekValue            -> state
  | Error  :                                 state
  | Halt   : cekValue                     -> state.

Fixpoint if_bound_otherwise_error (s : stack) (ρ : environment) (x : string) {struct ρ} : state :=
  match ρ with
  | EmptyEnvironment            => Error
  | NonEmptyEnvironment ρ' x' V =>
      if Strings.String.eqb x x'
        then Return s V
        else if_bound_otherwise_error s ρ' x
  end.

Definition state_with_trace := writer (list unicodestring) state.

Definition if_argV_otherwise_error (s : state_with_trace) (ι : expectedBuiltinArg) : state_with_trace :=
  match ι with
  | ArgV => s
  | ArgQ => mreturn Error
  end.

Definition if_argQ_otherwise_error (s : state_with_trace) (ι : expectedBuiltinArg) : state_with_trace :=
  match ι with
  | ArgQ => s
  | ArgV => mreturn Error
  end.

Definition unfold_case (s : stack) (i : N) (Ms : list term) (Vs : list cekValue) (ρ : environment) : state :=
  match nth_error Ms (N.to_nat i) with
  | Some m_i => let s_out := fold_left (fun s_j V => LeftApplicationToValue V :: s_j) Vs s in
                Eval s_out ρ m_i
  | None     => Error
  end.

Definition eval_builtin (s : stack) (b : builtinFun) (Vs : list cekValue) : state_with_trace :=
  (
    a <- evaluate_builtin_function b Vs ;;
    match a with
    | Some V => mreturn (Return s V)
    | None   => mreturn Error
    end
  )%monad.

Module CekNotations.
  Declare Scope cek_scope.
  Delimit Scope cek_scope with cek.

  (* State *)
  Notation "s ; ρ ▷ M" := (Eval   s ρ M) (at level 99) : cek_scope.
  Notation "s ◁ V"     := (Return s V)   (at level 99) : cek_scope.
  Notation "◆"         := (Error)        (at level 99) : cek_scope.
  Notation "▢ V"       := (Halt V)       (at level 99) : cek_scope.

  (* Value *)
  Notation "'v' ⟨ 'con' 'T' c ⟩"           := (VCon c)           (at level 99) : cek_scope.
  Notation "'v' ⟨ 'lam' x , M , ρ ⟩"       := (VLam x M ρ)       (at level 99) : cek_scope.
  Notation "'v' ⟨ 'delay' M , ρ ⟩"         := (VDelay M ρ)       (at level 99) : cek_scope.
  Notation "'v' ⟨ 'constr' i , Vs ⟩"       := (VConstr i Vs)     (at level 99) : cek_scope.
  Notation "'v' ⟨ 'builtin' b , Vs , As ⟩" := (VBuiltin b Vs As) (at level 99) : cek_scope.

  (* UPLC *)
  Notation "'u' ( 'var' x )"         := (Var x)       (at level 99) : cek_scope.
  Notation "'u' ( 'con' 'T' c )"     := (Const c)     (at level 99) : cek_scope.
  Notation "'u' ( 'lam' x , M )"     := (Lam x M)     (at level 99) : cek_scope.
  Notation "'u' ( 'delay' M )"       := (Delay M)     (at level 99) : cek_scope.
  Notation "'u' ( 'force' M )"       := (Force M)     (at level 99) : cek_scope.
  Notation "'u' [ M ∘ N ]"           := (Apply M N)   (at level 99) : cek_scope.
  Notation "'u' ( 'constr' i , Ms )" := (Constr i Ms) (at level 99) : cek_scope.
  Notation "'u' ( 'case' N , Ms )"   := (Case N Ms)   (at level 99) : cek_scope.
  Notation "'u' ( 'builtin' b )"     := (Builtin b)   (at level 99) : cek_scope.
  Notation "'u' ( 'error' )"         := (Term.Error)  (at level 99) : cek_scope.

  (* Frame *)
  Notation "'f' ( 'force' ⎵ )"                   := (ForceFrame)                   (at level 99) : cek_scope.
  Notation "'f' [ ⎵ ( M , ρ ) ]"                 := (LeftApplicationToTerm M ρ)    (at level 99) : cek_scope.
  Notation "'f' [ ⎵ V ]"                         := (LeftApplicationToValue V)     (at level 99) : cek_scope.
  Notation "'f' [ V ⎵ ]"                         := (RightApplicationOfValue V)    (at level 99) : cek_scope.
  Notation "'f' ( 'constr' i , V ⎵ ( Ms , ρ ) )" := (ConstructorArgument i V Ms ρ) (at level 99) : cek_scope.
  Notation "'f' ( 'case' ⎵ ( M , ρ ) )"          := (CaseScrutinee M ρ)            (at level 99) : cek_scope.

  (* List *)
  Notation "x ⋅ xs"  := (x :: xs)    (at level 99) : cek_scope.
  Notation "xs :⋅ x" := (app xs [x]) (at level 99) : cek_scope.

  (* Environment *)
  Notation "s ◁ 'ρ' '⟦' x '⟧' 'if' 'x' 'is' 'bound' 'in' ρ" := (if_bound_otherwise_error s ρ x) (at level 99) : cek_scope.
  Notation "ρ '⟦' x ↦ V '⟧'"                                := (NonEmptyEnvironment ρ x V)      (at level 99) : cek_scope.

  (* Builtins *)
  Notation "s 'if' i '∈' '𝓤' '∪' '𝓥'" := (if_argV_otherwise_error s i) (at level 99) : cek_scope.
  Notation "s 'if' i '∈' '𝓠'"         := (if_argQ_otherwise_error s i) (at level 99) : cek_scope.
  Notation "'Eval_CEK' ( s , b , Vs )" := (eval_builtin s b Vs) : cek_scope.
End CekNotations.

Import CekNotations.
Local Open Scope cek_scope.
Local Open Scope builtin_scope.

Import ExpectedArgNotations.
Local Open Scope expectedArgs_scope.

Local Definition writer_state (s : state) : state_with_trace := mreturn s.
Local Coercion writer_state : state >-> state_with_trace.

Definition step (Σ : state) : state_with_trace :=
  match Σ with
  |                               s; ρ ▷ u(var x)                  => s ◁ ρ⟦x⟧ if x is bound in ρ
  |                               s; ρ ▷ u(con T c)                => s ◁ v⟨con T c⟩
  |                               s; ρ ▷ u(lam x, M)               => s ◁ v⟨lam x, M, ρ⟩
  |                               s; ρ ▷ u(delay M)                => s ◁ v⟨delay M, ρ⟩
  |                               s; ρ ▷ u(force M)                =>  f(force ⎵) ⋅ s; ρ ▷ M
  |                               s; ρ ▷ u[M ∘ N]                  => f[⎵ (N, ρ)] ⋅ s; ρ ▷ M
  |                               s; ρ ▷ u(constr i, (M ⋅ Ms))     => f(constr i, [] ⎵ (Ms, ρ)) ⋅ s; ρ ▷ M
  |                               s; ρ ▷ u(constr i, [])           => s ◁ v⟨constr i, []⟩
  |                               s; ρ ▷ u(case N, Ms)             => f(case ⎵ (Ms, ρ)) ⋅ s; ρ ▷ N
  |                               s; ρ ▷ u(builtin b)              => s ◁ v⟨builtin b, [], α(b)⟩
  |                               s; ρ ▷ u(error)                  => ◆
  |                                 [] ◁ V                         => ▢ V
  |                    f[⎵ (M, ρ)] ⋅ s ◁ V                         => f[V ⎵] ⋅ s; ρ ▷ M
  |            f[v⟨lam x, M, ρ⟩ ⎵] ⋅ s ◁ V                         => s; ρ⟦x ↦ V⟧ ▷ M
  |                         f[⎵ V] ⋅ s ◁ v⟨lam x, M, ρ⟩            => s; ρ⟦x ↦ V⟧ ▷ M
  |   f[v⟨builtin b, Vs, ι ⊙ η⟩ ⎵] ⋅ s ◁ V                         => (s ◁ v⟨builtin b, Vs :⋅ V, η⟩) if ι ∈ 𝓤 ∪ 𝓥
  |                         f[⎵ V] ⋅ s ◁ v⟨builtin b, Vs, ι ⊙ η⟩   => (s ◁ v⟨builtin b, Vs :⋅ V, η⟩) if ι ∈ 𝓤 ∪ 𝓥
  |    f[v⟨builtin b, Vs, a[ι]⟩ ⎵] ⋅ s ◁ V                         => (Eval_CEK(s, b, Vs :⋅ V)) if ι ∈ 𝓤 ∪ 𝓥
  |                         f[⎵ V] ⋅ s ◁ v⟨builtin b, Vs, a[ι]⟩    => (Eval_CEK(s, b, Vs :⋅ V)) if ι ∈ 𝓤 ∪ 𝓥
  |                     f(force ⎵) ⋅ s ◁ v⟨delay M, ρ⟩             => s; ρ ▷ M
  |                     f(force ⎵) ⋅ s ◁ v⟨builtin b, Vs, ι ⊙ η⟩   => (s ◁ v⟨builtin b, Vs, η⟩) if ι ∈ 𝓠
  |                     f(force ⎵) ⋅ s ◁ v⟨builtin b, Vs, a[ι]⟩    => (Eval_CEK(s, b, Vs)) if ι ∈ 𝓠
  |  f(constr i, Vs ⎵ (M ⋅ Ms, ρ)) ⋅ s ◁ V                         => f(constr i, Vs :⋅ V ⎵ (Ms, ρ)) ⋅ s; ρ ▷ M
  |      f(constr i, Vs ⎵ ([], ρ)) ⋅ s ◁ V                         => s ◁ v⟨constr i, Vs :⋅ V⟩
  |              f(case ⎵ (Ms, ρ)) ⋅ s ◁ v⟨constr i, Vs⟩           => unfold_case s i Ms Vs ρ
  | _ => ◆
  end.


Fixpoint run_steps (s : state_with_trace) (n : nat) {struct n} : state_with_trace :=
  match n, s with
  | _  , Writer _ _ (▢ V) _ => s
  | _  , Writer _ _ (◆)   _ => s
  | 0  , _                   => s
  | S p, _                   => mbind s (fun x => run_steps (step x) p)
  end.

Fixpoint apply_params (body : term) (params : list term) {struct params} : term :=
  match params with
  | h :: t => apply_params (Apply body h) t
  | _      => body
  end.

Definition initial_state (t : term) : state_with_trace := Writer _ _ ([]; EmptyEnvironment ▷ t) [].

Local Open Scope functional_scope.

Definition cek_execute_program (p : program) (params : list term) (n : nat) : state * (list unicodestring) :=
  match p with
  | Program (Version 1 1 0) body => let (final_state, trace) := run_steps (apply_params body params |> initial_state) n in
                                    (final_state, trace)
  | _                            => (Error, ["unknown program version"%unicode])
  end.
