From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Prelude.FunctionalNotations.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Local Open Scope functional_scope.

Definition chooseList (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstList []); nil_case; _        ] => Some nil_case
   | [VCon (ConstList _ ); _       ; cons_case] => Some cons_case
   | _                                          => None
   end.

Definition mkCons (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon x; VCon (ConstList xs)] => x :: xs |> cekValue_of_list |> Some
   | _                             => None
   end.

Definition headList (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstList (x :: _))] => x |> VCon |> Some
   | _                           => None
   end.

Definition tailList (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstList (_ :: xs))] => xs |> cekValue_of_list |> Some
   | _                            => None
   end.

Definition nullList (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstList [])] => true  |> cekValue_of_boolean |> Some
   | [VCon (ConstList _ )] => false |> cekValue_of_boolean |> Some
   | _                     => None
   end.
