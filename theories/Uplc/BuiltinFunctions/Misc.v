From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Prelude.List.
From CoqUplc Require Import Prelude.Monad.
                     Import MonadNotations.

From CoqUplc Require Import Unicode.String.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Definition chooseUnit (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon Unit; val] => Some val
   | _                => None
   end.

Definition trace (Vs : list cekValue) : writer (list unicodestring) (option cekValue) :=
  match Vs with
  | [VCon (ConstString x); val] => (tell [x] ;; mreturn (Some val))%monad
  | _                           => mreturn None
  end.
