From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.FunctionalNotations.

From CoqUplc Require Import PlutusV3.CekValue.
From CoqUplc Require Import PlutusV3.Uplc.

Local Open Scope Z_scope.
Local Open Scope functional_scope.

Definition addInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_integer (x + y))
   | _                                    => None
   end.

Definition subtractInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_integer (x - y))
   | _                                    => None
   end.

Definition multiplyInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_integer (x * y))
   | _                                    => None
   end.

Definition divideInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer a); VCon (Integer 0)] => None
   | [VCon (Integer a); VCon (Integer b)] => let d := Z.abs (Z.div a b) in
                                             match a >=? 0, b >=? 0 with
                                             | true , true  => d
                                             | false, true  => -d
                                             | true , false => -d
                                             | false, false => d
                                             end |> cekValue_of_integer |> Some
   | _                                    => None
   end.

Definition modInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer a); VCon (Integer 0)] => None
   | [VCon (Integer a); VCon (Integer b)] => let m := Z.abs (Z.modulo a b) in
                                             match a >=? 0, b >=? 0 with
                                             | true , true  => m
                                             | false, true  => m
                                             | true , false => m
                                             | false, false => -m
                                             end |> cekValue_of_integer |> Some
   | _                                    => None
   end.

Definition quotientInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer a); VCon (Integer 0)] => None
   | [VCon (Integer a); VCon (Integer b)] => let q := Z.abs (Z.quot a b) in
                                             match a >=? 0, b >=? 0 with
                                             | true , true  => q
                                             | false, true  => -q
                                             | true , false => q
                                             | false, false => q
                                             end |> cekValue_of_integer |> Some
   | _                                    => None
   end.

Definition remainderInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer a); VCon (Integer 0)] => None
   | [VCon (Integer a); VCon (Integer b)] => let r := Z.abs (Z.rem a b) in
                                             match a >=? 0, b >=? 0 with
                                             | true , true  => r
                                             | false, true  => -r
                                             | true , false => r
                                             | false, false => -r
                                             end |> cekValue_of_integer |> Some
   | _                                    => None
   end.

Definition equalsInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_boolean (x =? y))
   | _                                    => None
   end.

Definition lessThanInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_boolean (x <? y))
   | _                                    => None
   end.

Definition lessThanEqualsInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (cekValue_of_boolean (x <=? y))
   | _                                    => None
   end.

Local Definition exp_mod (a : Z) (e m : positive) : Z := a ^ (Zpos e) mod (Zpos m).

Local Definition exp_mod_inverse (a : Z) (e m' : positive) : option Z :=
  let m := Zpos m' in
  match Z.gcd a m with
  | 1 => Some ((a ^ (Zpos e)) ^ (m - 2) mod m)
  | _ => None
  end.

Definition expModInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer a); VCon (Integer  Z0     ); VCon (Integer (Zpos m))] => 1             |> cekValue_of_integer |> Some
   | [VCon (Integer a); VCon (Integer (Zpos e)); VCon (Integer (Zpos m))] => exp_mod a e m |> cekValue_of_integer |> Some
   | [VCon (Integer a); VCon (Integer (Zneg e)); VCon (Integer (Zpos m))] => option_map (cekValue_of_integer) (exp_mod_inverse a e m)
   | _                                                                    => None
   end.
