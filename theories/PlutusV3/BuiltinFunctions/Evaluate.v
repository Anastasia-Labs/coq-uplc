From CoqUplc Require Import PlutusV3.CekValue.
From CoqUplc Require Import PlutusV3.Uplc.

From CoqUplc Require Import PlutusV3.BuiltinFunctions.Bool.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.Integer.

Definition evaluate_builtin_function (b : builtinFun) : list cekValue -> option cekValue :=
  match b with
  | SubtractInteger => subtractInteger
  | LessThanInteger => lessThanInteger
  | IfThenElse      => ifThenElse
  | _               => fun _ => None
  end.
