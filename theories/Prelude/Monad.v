
Class Semigroup (A : Type) := {
  sconcat : A -> A -> A
}.

Class Monoid (A : Type) `(S : Semigroup A) := {
  mempty : A
}.

Class Monad (M : Type -> Type) := {
  mbind   : forall {A B : Type}, M A -> (A -> M B) -> M B
; mreturn : forall {A   : Type}, A -> M A
}.

Module MonadNotations.
  Declare Scope monad_scope.
  Delimit Scope monad_scope with monad.

  Notation "x <- m1 ;; m2" := (mbind m1 (fun x => m2)) (at level  75, right associativity, m1 at next level) : monad_scope.
  Notation      "m1 ;; m2" := (mbind m1 (fun _ => m2)) (at level 100, right associativity)                   : monad_scope.
End MonadNotations.

Inductive writer (W A : Type) := Writer (a : A) (w : W).

Instance monad_writer {W : Type} `{Monoid W} : Monad (writer W) := {
  mbind   := fun {A} {B} ma f => let (a, w0) := ma  in
                                 let (b, w1) := f a in
                                 Writer W B b (sconcat w0 w1)
; mreturn := fun {A} a => Writer W A a mempty
}.

Definition tell {W : Type} (w : W) : writer W unit :=
  Writer W unit tt w.
