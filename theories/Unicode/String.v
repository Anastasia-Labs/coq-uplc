From Coq Require Import NArith.
From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Prelude.Monad.

Inductive unicodestring : Set := Unicode (chars : list N).

Definition append (a b : unicodestring) : unicodestring :=
  let (a') := a in
  let (b') := b in
  Unicode (app a' b').

Fixpoint eqb_list (a b : list N) {struct a} : bool :=
  match a, b with
  | [], []             => true
  | [], _              => false
  | _ , []             => false
  | ha :: ta, hb :: tb => andb (N.eqb ha hb) (eqb_list ta tb)
  end.

Definition eqb (a b : unicodestring) : bool :=
  let (a') := a in
  let (b') := b in
  eqb_list a' b'.

Instance semigroup_unicodestring : Semigroup unicodestring := {
  sconcat := fun a b => append a b
}.

Instance monoid_unicodestring : Monoid unicodestring _ := {
  mempty := Unicode []
}.
