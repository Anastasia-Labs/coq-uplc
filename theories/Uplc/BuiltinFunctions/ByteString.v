From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.Bytes.
From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.Option.

From CoqUplc Require Import Uplc.CekValue.
From CoqUplc Require Import Uplc.Term.

Local Open Scope string_scope.
Local Open Scope functional_scope.

Definition appendByteString (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (ByteString x); VCon (ByteString y)] => append x y |> cekValue_of_byteString |> Some
   | _                                          => None
   end.

Definition consByteString_variant1 (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer x); VCon (ByteString y)] => match Z.modulo x 256 with
                                                | Z0     => String.String Ascii.zero             y |> cekValue_of_byteString |> Some
                                                | Zpos p => String.String (Ascii.ascii_of_pos p) y |> cekValue_of_byteString |> Some
                                                | Zneg p => None (* impossible case *)
                                                end
   | _                                       => None
   end.

Definition consByteString_variant2 (Vs : list cekValue) : option cekValue :=
   match Vs with
   | [VCon (Integer Z0      ); VCon (ByteString y)] => String.String Ascii.zero y |> cekValue_of_byteString |> Some
   | [VCon (Integer (Zpos p)); VCon (ByteString y)] => if (p <=? 255)%positive
                                                         then String.String (Ascii.ascii_of_pos p) y |> cekValue_of_byteString |> Some
                                                         else None
   | _                                              => None
   end.

Definition sliceByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer i); VCon (Integer l); VCon (ByteString b)] => substring (Z.to_nat i) (Z.to_nat l) b |> cekValue_of_byteString |> Some
   | _                                                         => None
   end.

Definition lengthOfByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b)] => Z.of_nat (length b) |> cekValue_of_integer |> Some
   | _                     => None
   end.

Definition Z_of_ascii (x : ascii) : Z := x |> N_of_ascii |> Z.of_N.

Definition indexByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer Z0      ); VCon (ByteString b)] => String.get 0              b |> option_map (Z_of_ascii >> cekValue_of_integer)
   | [VCon (Integer (Zpos p)); VCon (ByteString b)] => String.get (Pos.to_nat p) b |> option_map (Z_of_ascii >> cekValue_of_integer)
   | _                                              => None
   end.

Definition equalsByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString x); VCon (ByteString y)] => x =? y |> cekValue_of_boolean |> Some
   | _                                          => None
   end.

Definition lessThanByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString x); VCon (ByteString y)] => x <? y |> cekValue_of_boolean |> Some
   | _                                          => None
   end.

Definition lessThanEqualsByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString x); VCon (ByteString y)] => x <=? y |> cekValue_of_boolean |> Some
   | _                                          => None
   end.

Definition integerToByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Bool e); VCon (Integer w); VCon (Integer n)] => option_map cekValue_of_byteString (integer_to_bytestring e w n)
   | _                                                   => None
   end.

Definition byteStringToInteger (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Bool e); VCon (ByteString s)] => bytestring_to_integer e s |> Z.of_N |> cekValue_of_integer |> Some
   | _                                    => None
   end.

Definition andByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Bool e); VCon (ByteString b1); VCon (ByteString b2)] => and_bytestring e b1 b2 |> cekValue_of_byteString |> Some
   | _                                                           => None
   end.

Definition orByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Bool e); VCon (ByteString b1); VCon (ByteString b2)] => or_bytestring e b1 b2 |> cekValue_of_byteString |> Some
   | _                                                           => None
   end.

Definition xorByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Bool e); VCon (ByteString b1); VCon (ByteString b2)] => xor_bytestring e b1 b2 |> cekValue_of_byteString |> Some
   | _                                                           => None
   end.

Definition complementByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b)] => xor_bytestring false b (extend_to ""%string (length b) "255"%char) |> cekValue_of_byteString |> Some
   | _                     => None
   end.

Definition shiftByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b); VCon (Integer Z0      )] => b                                 |> cekValue_of_byteString |> Some
   | [VCon (ByteString b); VCon (Integer (Zpos p))] => shift_bits_right b (Pos.to_nat p) |> cekValue_of_byteString |> Some
   | [VCon (ByteString b); VCon (Integer (Zneg p))] => shift_bits_left  b (Pos.to_nat p) |> cekValue_of_byteString |> Some
   | _                                              => None
   end.

Definition rotateByteString (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b); VCon (Integer Z0      )] => b                                  |> cekValue_of_byteString |> Some
   | [VCon (ByteString b); VCon (Integer (Zpos p))] => rotate_bits_right b (Pos.to_nat p) |> cekValue_of_byteString |> Some
   | [VCon (ByteString b); VCon (Integer (Zneg p))] => rotate_bits_left  b (Pos.to_nat p) |> cekValue_of_byteString |> Some
   | _                                        => None
   end.

Definition countSetBits (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b)] => count_set_bits b |> Z.of_nat |> cekValue_of_integer |> Some
   | _                     => None
   end.

Definition findFirstSetBit (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b)] => first_set_bit b |> cekValue_of_integer |> Some
   | _                     => None
   end.

Definition readBit (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b); VCon (Integer Z0      )] => option_map cekValue_of_boolean (read_bit b 0)
   | [VCon (ByteString b); VCon (Integer (Zpos p))] => option_map cekValue_of_boolean (read_bit b (Pos.to_nat p))
   | _                                              => None
   end.

Local Fixpoint list_integer_of_const_list (l : list const) : option (list Z) :=
  match l with
  | Integer z :: t => option_map (cons z) (list_integer_of_const_list t)
  | _         :: t => None
  | []             => Some []
  end.

Definition writeBits (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (ByteString b); VCon (ConstList l); VCon (Bool u)] =>
       let r := option_flatmap (write_bits b u) (list_integer_of_const_list l) in
       option_map (cekValue_of_byteString) r
   | _                                                        => None
   end.

Definition replicateByte (Vs : list cekValue) : option cekValue :=
  match Vs with
   | [VCon (Integer l); VCon (Integer b)] => option_map (cekValue_of_byteString) (replicate_bytes l b)
   | _                                    => None
   end.
