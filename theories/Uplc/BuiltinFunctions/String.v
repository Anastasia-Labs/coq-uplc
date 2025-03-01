From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Prelude.FunctionalNotations.

From CoqUplc Require Import Unicode.String.
From CoqUplc Require Import Unicode.Utf8Encoding.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Local Open Scope string_scope.
Local Open Scope functional_scope.

Definition appendString (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstString x); VCon (ConstString y)] => append x y |> cekValue_of_string |> Some
   | _                                            => None
   end.

Definition equalsString (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstString x); VCon (ConstString y)] => eqb x y |> cekValue_of_boolean |> Some
   | _                                            => None
   end.

Definition encodeUtf8 (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ConstString x)] => option_map cekValue_of_byteString (encode_utf8 x)
   | _                      => None
   end.

Definition decodeUtf8 (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ByteString x)] => option_map cekValue_of_string (decode_utf8 x)
   | _                     => None
   end.
