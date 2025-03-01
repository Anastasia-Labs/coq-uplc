From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Definition ifThenElse (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Bool b); case_true; case_false] => Some (if b then case_true else case_false)
   | _                                      => None
   end.
