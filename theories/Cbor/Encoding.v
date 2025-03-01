From Coq Require Import FunInd.
From Coq Require Import funind.Recdef.
From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.Bytes.
From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.Option.

From CoqUplc Require Import Uplc.Term.

Local Open Scope bool_scope.
Local Open Scope N_scope.
Local Open Scope functional_scope.

Local Definition string_cons (x y : string) : string := concat "" [x; y].
Local Notation "x ⋅ y" := (string_cons x y) (at level 99).


Local Definition b_ (i n : N) : ascii :=
  let p := N.pow 256 i in
  ascii_of_N (N.div n p).

Local Definition e_1 (n : N) : list ascii := [b_ 0 n].
Local Definition e_2 (n : N) : list ascii := [b_ 1 n; b_ 0 n].
Local Definition e_4 (n : N) : list ascii := [b_ 3 n; b_ 2 n; b_ 1 n; b_ 0 n].
Local Definition e_8 (n : N) : list ascii := [b_ 7 n; b_ 6 n; b_ 5 n; b_ 4 n; b_ 3 n; b_ 2 n; b_ 1 n; b_ 0 n].

Local Example e_8_ex1 : string_of_list_ascii (e_8 7234295460216005990) = "deadbeef"%string. Proof eq_refl.


Local Definition head_first_byte (m n : N) : ascii :=
  ascii_of_N (32 * m + n).

Local Definition encode_head (m n : N) : option string :=
  let fb := head_first_byte m in
  if m <=? 7 then
         if n <=?                   23 then Some (string_of_list_ascii [fb n])
    else if n <=?                  255 then Some (string_of_list_ascii (fb 24 :: e_1 n))
    else if n <=?                65535 then Some (string_of_list_ascii (fb 25 :: e_2 n))
    else if n <=?           4294967295 then Some (string_of_list_ascii (fb 26 :: e_4 n))
    else if n <=? 18446744073709551615 then Some (string_of_list_ascii (fb 27 :: e_8 n))
    else None
  else None.


Local Open Scope nat_scope.

Local Lemma length_substing_le : forall (s : string) (n m : nat), length (substring n m s) <= length s.
  induction s; induction m; induction n; simpl; auto with arith.
Qed.

Function split_to_chunks (s : string) {measure length s} : list string :=
  match s with
  | String a s' => substring 0 64 s :: split_to_chunks (substring 64 (length s) s)
  | EmptyString => []
  end.
Proof.
  intros s a s' Hs; simpl; unfold lt; apply le_n_S; apply length_substing_le.
Defined.

Local Close Scope nat_scope.

Local Example split_to_chunks_ex1 : split_to_chunks "1234567890123456789012345678901234567890123456789012345678901234"%string =
  [ "1234567890123456789012345678901234567890123456789012345678901234"%string ]. Proof eq_refl.
Local Example split_to_chunks_ex2 : split_to_chunks "12345678901234567890123456789012345678901234567890123456789012345"%string =
  [ "1234567890123456789012345678901234567890123456789012345678901234"%string
  ; "5"%string
  ]. Proof eq_refl.
Local Example split_to_chunks_ex3 : split_to_chunks "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456"%string =
  [ "1234567890123456789012345678901234567890123456789012345678901234"%string
  ; "1234567890123456789012345678901234567890123456789012345678901234"%string
  ; "56"%string
  ]. Proof eq_refl.


Local Definition encode_indef (m : N) : ascii := head_first_byte m 31.

Local Definition encode_bytestring_chunk (s : string) : option string :=
  option_map (fun h => string_cons h s) (encode_head 2 (length s |> N.of_nat)).

Local Definition list_of_option {A : Type}  (x : option A) : list A :=
  match x with
  | Some v => [v]
  | None   => []
  end.

Local Definition encode_bytestring (s : string) : option string :=
  match split_to_chunks s with
  | []      => Some ""%string
  | h :: [] => encode_bytestring_chunk h
  | chunks  => Some (concat "" (string_of_list_ascii [encode_indef 2] :: flat_map (encode_bytestring_chunk >> list_of_option) chunks ++ [string_of_list_ascii ["255"%char]]))
  end.

Local Example encode_bytestring_ex1 : encode_bytestring "1234567890123456789012345678901234567890123456789012345678901234"%string =
  Some (concat "" [ string_of_list_ascii ["088"%char; "064"%char]; "1234567890123456789012345678901234567890123456789012345678901234"%string]). Proof eq_refl.
Local Example encode_bytestring_ex2 : encode_bytestring "12345678901234567890123456789012345678901234567890123456789012345"%string =
  Some (concat "" [ string_of_list_ascii ["095"%char]
                  ; string_of_list_ascii ["088"%char; "064"%char]; "1234567890123456789012345678901234567890123456789012345678901234"%string
                  ; string_of_list_ascii ["065"%char]; "5"%string
                  ; string_of_list_ascii ["255"%char]
                  ]). Proof eq_refl.
Local Example encode_bytestring_ex3 : encode_bytestring "1234567890123456789012345678901234567890123456789012345678901234123456789012345678901234567890123456789012345678901234567890123456"%string =
  Some (concat "" [ string_of_list_ascii ["095"%char]
                  ; string_of_list_ascii ["088"%char; "064"%char]; "1234567890123456789012345678901234567890123456789012345678901234"%string
                  ; string_of_list_ascii ["088"%char; "064"%char]; "1234567890123456789012345678901234567890123456789012345678901234"%string
                  ; string_of_list_ascii ["066"%char]; "56"%string
                  ; string_of_list_ascii ["255"%char]
                  ]). Proof eq_refl.

Local Open Scope Z_scope.

Local Definition encode_Z (n : Z) : option string :=
       if (                    0 <=? n) && (n <=?  18446744073709551615) then encode_head 0 (Z.to_N n)
  else if ( 18446744073709551616 <=? n                                 ) then option_flatmap2 (string_cons >>> Some) (encode_head 6 2) (n |> Z.to_N |> bytestring_of_N_be |> encode_bytestring)
  else if (-18446744073709551616 <=? n) && (n <=?                    -1) then encode_head 1 ((-n - 1) |> Z.to_N)
  else if (                                 n <=? -18446744073709551617) then option_flatmap2 (string_cons >>> Some) (encode_head 6 3) ((-n - 1) |> Z.to_N |> bytestring_of_N_be |> encode_bytestring)
  else None.


Local Definition encode_ctag (i : Z) : option string :=
       if (0 <=? i) && (i <=?   6) then encode_head 6 (121 + i |> Z.to_N)
  else if (7 <=? i) && (i <=? 127) then encode_head 6 (1280 + (i - 7) |> Z.to_N)
  else option_flatmap3 ((string_cons >>> string_cons) >>>> Some) (encode_head 6 102) (encode_head 4 2) (encode_Z i).

Fixpoint encode_data (d : data) {struct d} : option string :=
  match d with
  | DataConstr i l =>
      let l_e := flat_map (encode_data >> list_of_option) l in
      option_map (fun e_ctag => concat "" (e_ctag :: [string_of_list_ascii [encode_indef 4]] ++ l_e ++ [string_of_list_ascii ["255"%char]])) (encode_ctag i)
  | Map        l   =>
      let l_e := flat_map (fun p => option_flatmap2 (string_cons >>> Some) (encode_data (fst p)) (encode_data (snd p)) |> list_of_option) l in
      option_map (fun h => concat "" (h :: l_e)) (encode_head 5 (List.length l |> N.of_nat))
  | DataList   l   =>
      let l_e := flat_map (encode_data >> list_of_option) l in
      Some (concat "" (string_of_list_ascii [encode_indef 4] :: l_e ++ [string_of_list_ascii ["255"%char]]))
  | I          n   => encode_Z n
  | B          s   => encode_bytestring s
  end.

From Coq Require Import Init.Byte.


Local Definition of_hexstring (bs : list byte) : string :=
  map ascii_of_byte bs |> string_of_list_ascii.

Local Example encode_data_exZ1 : encode_data (I 12) = Some (string_of_list_ascii ["012"%char]). Proof eq_refl.
Local Example encode_data_exZ2 : encode_data (I 42) = Some (string_of_list_ascii ["024"%char; "042"%char]). Proof eq_refl.

Local Example encode_data_ex1 :
    encode_data (
      DataConstr 0 [
        DataConstr 0 [I 1284531];
        I 1739713998000
      ]
    ) = Some (of_hexstring [ xd8; x79; x9f; xd8; x79; x9f; x1a; x00; x13; x99; xb3; xff
                           ; x1b; x00; x00; x01; x95; x0f; x08; xec; xb0; xff]).
Proof eq_refl.

Local Example encode_data_ex2 :
  encode_data (
    DataConstr 0 [
      I 144375414;
      I 22710;
      I 4387720097
    ]
  ) = Some (of_hexstring [xd8; x79; x9f; x1a; x08; x9a; xfe; x76; x19; x58; xb6; x1b; x00; x00; x00; x01; x05; x87; x4b; xa1; xff]).
Proof eq_refl.

