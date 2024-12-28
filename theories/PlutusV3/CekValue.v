From Coq Require Import Strings.String.

From CoqUplc Require Import PlutusV3.Builtins.
From CoqUplc Require Import PlutusV3.Uplc.

Inductive cekValue : Set :=
  | VCon     : const                                              -> cekValue
  | VDelay   :           term -> environment                      -> cekValue
  | VLam     : string -> term -> environment                      -> cekValue
  | VConstr  : nat        -> list cekValue                        -> cekValue
  | VBuiltin : builtinFun -> list cekValue -> expectedBuiltinArgs -> cekValue

with environment : Set :=
  | NonEmptyEnvironment : environment -> string -> cekValue -> environment
  | EmptyEnvironment    :                                      environment.
