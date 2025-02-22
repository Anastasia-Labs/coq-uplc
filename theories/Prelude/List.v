From Coq Require Import Lists.List.

From CoqUplc Require Import Prelude.Monad.

Instance semigroup_list {A : Type} : Semigroup (list A) := {
  sconcat := fun a b => app a b
}.

Instance monoid_list {A : Type} : Monoid (list A) _ := {
  mempty := nil
}.
