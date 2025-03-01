From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Definition fstPair (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Pair x _)] => Some (VCon x)
   | _                 => None
   end.

Definition sndPair (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Pair _ y)] => Some (VCon y)
   | _                 => None
   end.
