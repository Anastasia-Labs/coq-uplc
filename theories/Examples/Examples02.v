From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.Byte.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Unicode.String.
From CoqUplc Require Import Unicode.StringShow.

From CoqUplc Require Import Uplc.CekMachine.
From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Module ExampleNotations.
  Definition const_of_bytes (b : list byte) : const := ByteString (string_of_list_ascii (map ascii_of_byte b)).
  
  Declare Scope exampleNotation_scope.
  Delimit Scope exampleNotation_scope with exampleNotation.

  Notation "'plutusV3' x"          := (Program (Version 1 1 0) x)    (at level 89, left associativity) : exampleNotation_scope.

  Notation "'\' x '=>' y"          := (Lam x y)                      (at level 89) : exampleNotation_scope.
  Notation "'\' x '\' y '=>' z"    := (Lam x (Lam y z))              (at level 89) : exampleNotation_scope.
  Notation "x '#' y"               := (Apply x y)                    (at level 88, left associativity) : exampleNotation_scope.
  Notation "'val' x '<-' y 'in' z" := (Apply (Lam x z) y)            (at level 89) : exampleNotation_scope.
  Notation "'value' x"             := (Var x)                        (at level 87) : exampleNotation_scope.
  
  Notation "'byteStringToInteger'" := (Builtin ByteStringToInteger)  (at level 87) : exampleNotation_scope.
  Notation "'decodeUtf8'"          := (Builtin DecodeUtf8)           (at level 87) : exampleNotation_scope.
  Notation "'expMod'"              := (Builtin ExpModInteger)        (at level 87) : exampleNotation_scope.
  Notation "'findFirstSetBit'"     := (Builtin FindFirstSetBit)      (at level 87) : exampleNotation_scope.
  Notation "'integerToByteString'" := (Builtin IntegerToByteString)  (at level 87) : exampleNotation_scope.
  Notation "'replicateByte'"       := (Builtin ReplicateByte)        (at level 87) : exampleNotation_scope.
  Notation "'serialiseData'"       := (Builtin SerialiseData)        (at level 87) : exampleNotation_scope.
  Notation "'trace'"               := (Force (Builtin Trace))        (at level 87) : exampleNotation_scope.
  Notation "'writeBits'"           := (Builtin WriteBits)            (at level 87) : exampleNotation_scope.
  
  Notation "'t'"                   := (Const (Bool true))            (at level 87) : exampleNotation_scope.
  Notation "'con' x"               := (Const x)                      (at level 87) : exampleNotation_scope.
  Notation "'int' x"               := (Integer x)                    (at level 86) : exampleNotation_scope.
  Notation "'bytes' x"             := (const_of_bytes x)             (at level 86) : exampleNotation_scope.
  Notation "'data' x"              := (Data x)                       (at level 86) : exampleNotation_scope.
  Notation "'clist' x"             := (ConstList x)                  (at level 86) : exampleNotation_scope.

  Notation "'success' x"           := (Halt (VCon x), [])            (at level 89) : exampleNotation_scope.
  Notation "'succ:' x 'trace:' y"  := (Halt (VCon x), [y])           (at level 89) : exampleNotation_scope.
End ExampleNotations.

Import ExampleNotations.

Local Open Scope exampleNotation_scope.

(* serialiseData: batch 2 function *)
Definition serialiseData_program : program := plutusV3
  \"d" => serialiseData # value "d".

Example example_data :=
  DataList [ DataList [I 0; I 0; I 0; I 0; I 0]
           ; I 17
           ].

Property serialiseData_example :
    cek_execute_program serialiseData_program [con data example_data] 11 = success bytes [x9f; x9f; x00; x00; x00; x00; x00; xff; x11; xff].
Proof.
  compute. reflexivity.
Qed.


(* byteStringToInteger, integerToByteString: batch 4 function *)
Definition I_to_B_to_I_program : program := plutusV3
  \"i" =>
      val "b" <- integerToByteString # t # con int 7 # value "i" in
      trace # (decodeUtf8 # value "b") # (byteStringToInteger # t # value "b").

Property i_b_i_example :
  cek_execute_program I_to_B_to_I_program [con int 22637249857680191] 46 = succ: int 22637249857680191 trace: "Plutus?"%unicode.
Proof.
  compute. reflexivity.
Qed.


(* findFirstSetBit, replicateByte, writeBits: batch 5 functions *)
Definition find_first_index_program : program := plutusV3
  \"l" \"xs" =>
      val "bs" <- writeBits # (replicateByte # value "l" # con int 0) # value "xs" # t in
      findFirstSetBit # value "bs".

Property find_first_example :
    cek_execute_program find_first_index_program [con int 4; con clist [int 15; int 4]] 41 = success int 4.
Proof.
  compute. reflexivity.
Qed.


Definition expMod_program : program :=
  plutusV3 \"a" \"e" => expMod # value "a" # value "e" # con int 256.

Property expMod_example :
    cek_execute_program expMod_program [con int 2; con int 8] 24 = success int 0.
Proof eq_refl.
