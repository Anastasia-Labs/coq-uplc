From Coq Require Import Init.Decimal.
From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Numbers.DecimalString.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Open Scope string_scope.

Class Show (A : Type) := {
  show : A -> string
}.

#[export]
Instance show_uint : Show uint := {
  show := NilZero.string_of_uint
}.

#[export]
Instance show_int : Show int := {
  show := NilZero.string_of_int
}.

#[export]
Instance show_nat : Show nat := {
  show n := show (to_uint n)
}.

#[export]
Instance show_Z : Show Z := {
  show z := show (Z.to_int z)
}.

#[export]
Instance show_bool : Show bool := {
  show b := if b then "true" else "false"
}.

Definition showList {A : Type} (f : A -> string) (xs : list A) : string :=
  "[" ++ (concat "; " (map f xs)) ++ "]".

#[export]
Instance show_list {A : Type} `{Show A} : Show (list A) := {
  show := showList show
}.

Definition showPair {A B : Type} (fa : A -> string) (fb : B -> string) (p : A * B) : string :=
  let (a, b) := p in "(" ++ fa a ++ ", " ++ fb b ++ ")".

#[export]
Instance show_pair {A B : Type} `{Show A} `{Show B} : Show (A * B) := {
  show := showPair show show
}.
