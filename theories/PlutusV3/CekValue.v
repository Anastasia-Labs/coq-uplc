From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.FunctionalNotations.

From CoqUplc Require Import PlutusV3.Builtins.
From CoqUplc Require Import PlutusV3.Uplc.
From CoqUplc Require Import Unicode.String.

Inductive cekValue : Set :=
  | VCon     : const                                              -> cekValue
  | VDelay   :           term -> environment                      -> cekValue
  | VLam     : string -> term -> environment                      -> cekValue
  | VConstr  : N          -> list cekValue                        -> cekValue
  | VBuiltin : builtinFun -> list cekValue -> expectedBuiltinArgs -> cekValue

with environment : Set :=
  | NonEmptyEnvironment : environment -> string -> cekValue -> environment
  | EmptyEnvironment    :                                      environment.

Local Open Scope functional_scope.

Definition cekValue_of_integer    (x : Z)             : cekValue := Integer     x |> VCon.
Definition cekValue_of_byteString (x : string)        : cekValue := ByteString  x |> VCon.
Definition cekValue_of_string     (x : unicodestring) : cekValue := ConstString x |> VCon.
Definition cekValue_of_unit                           : cekValue :=          Unit |> VCon.
Definition cekValue_of_boolean    (x : bool)          : cekValue := Bool        x |> VCon.
Definition cekValue_of_list       (x : list const)    : cekValue := ConstList   x |> VCon.
Definition cekValue_of_pair       (x y : const)       : cekValue := Pair      x y |> VCon.
Definition cekValue_of_data       (x : data)          : cekValue := Data        x |> VCon.
