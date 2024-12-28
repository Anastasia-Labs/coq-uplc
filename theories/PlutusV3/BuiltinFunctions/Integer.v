From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import ZArith.

From CoqUplc Require Import PlutusV3.CekValue.
From CoqUplc Require Import PlutusV3.Uplc.

Local Open Scope Z_scope.

Definition subtractInteger (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (VCon (Integer (x - y)))
   | _                                    => None
   end.

Definition lessThanInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer x); VCon (Integer y)] => Some (VCon (Bool (x <=? y)))
   | _                                    => None
   end.
