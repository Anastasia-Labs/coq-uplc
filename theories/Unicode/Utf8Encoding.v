From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import NArith.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.

From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.Option.

From CoqUplc Require Import Unicode.String.

Local Open Scope N_scope.
Local Open Scope functional_scope.

Definition get_bits_4 (n : N) :=
  [N.testbit n 3; N.testbit n 2; N.testbit n 1; N.testbit n 0].

Local Notation "x !! y" := (nth y x false) (at level 99).
Local Notation "x +: y" := (String x y)    (at level 99, right associativity).

Local Definition create_byte (b : list bool) : ascii :=
  (Ascii (b !! 7) (b !! 6) (b !! 5) (b !! 4) (b !! 3) (b !! 2) (b !! 1) (b !! 0))%nat.

Local Example create_byte_ex1 : create_byte [false; true; true; false; false; false; false; true] = "a"%char. Proof eq_refl.


Local Definition encode_char_1 (n : N) : string :=
  String (ascii_of_N (N.modulo n 0x0080)) EmptyString.

Local Example encode_char_1_ex1 : encode_char_1  86 = "V"%string. Proof eq_refl.
Local Example encode_char_1_ex2 : encode_char_1 342 = "V"%string. Proof eq_refl.


Local Definition encode_char_2 (n : N) : string :=
  let x     := N.modulo (N.div n 0x100) 0x10 in
  let y     := N.modulo (N.div n  0x10) 0x10 in
  let z     := N.modulo n               0x10 in
  let xxxx  := get_bits_4 x                  in
  let yyyy  := get_bits_4 y                  in
  let zzzz  := get_bits_4 z                  in
  let byte1 := create_byte [true;  true;     false; xxxx !! 1;  xxxx !! 2; xxxx !! 3; yyyy !! 0; yyyy !! 1] in
  let byte2 := create_byte [true; false; yyyy !! 2; yyyy !! 3;  zzzz !! 0; zzzz !! 1; zzzz !! 2; zzzz !! 3] in
  byte1 +: byte2 +: "".

Local Example encode_char_2_ex1 : encode_char_2 961 = "ρ"%string. Proof eq_refl.


Local Definition encode_char_3 (n : N) : string :=
  let w     := N.modulo (N.div n 0x1000) 0x10 in
  let x     := N.modulo (N.div n  0x100) 0x10 in
  let y     := N.modulo (N.div n   0x10) 0x10 in
  let z     := N.modulo n                0x10 in
  let wwww  := get_bits_4 w                   in
  let xxxx  := get_bits_4 x                   in
  let yyyy  := get_bits_4 y                   in
  let zzzz  := get_bits_4 z                   in
  let byte1 := create_byte [true;  true;     true; false;       wwww !! 0; wwww !! 1; wwww !! 2; wwww !! 3] in
  let byte2 := create_byte [true; false; xxxx !! 0; xxxx !! 1;  xxxx !! 2; xxxx !! 3; yyyy !! 0; yyyy !! 1] in
  let byte3 := create_byte [true; false; yyyy !! 2; yyyy !! 3;  zzzz !! 0; zzzz !! 1; zzzz !! 2; zzzz !! 3] in
  byte1 +: byte2 +: byte3 +: "".

Local Example encode_char_3_ex1 : encode_char_3 0x13EB = "Ꮻ"%string. Proof eq_refl.


Local Definition encode_char_4 (n : N) : string :=
  let u     := N.modulo (N.div n 0x100000) 0x10 in
  let v     := N.modulo (N.div n  0x10000) 0x10 in
  let w     := N.modulo (N.div n   0x1000) 0x10 in
  let x     := N.modulo (N.div n    0x100) 0x10 in
  let y     := N.modulo (N.div n     0x10) 0x10 in
  let z     := N.modulo n                  0x10 in
  let uuuu  := get_bits_4 u                     in
  let vvvv  := get_bits_4 v                     in
  let wwww  := get_bits_4 w                     in
  let xxxx  := get_bits_4 x                     in
  let yyyy  := get_bits_4 y                     in
  let zzzz  := get_bits_4 z                     in
  let byte1 := create_byte [true;  true;     true;  true;           false; uuuu !! 3; vvvv !! 0; vvvv !! 1] in
  let byte2 := create_byte [true; false; vvvv !! 2; vvvv !! 3;  wwww !! 0; wwww !! 1; wwww !! 2; wwww !! 3] in
  let byte3 := create_byte [true; false; xxxx !! 0; xxxx !! 1;  xxxx !! 2; xxxx !! 3; yyyy !! 0; yyyy !! 1] in
  let byte4 := create_byte [true; false; yyyy !! 2; yyyy !! 3;  zzzz !! 0; zzzz !! 1; zzzz !! 2; zzzz !! 3] in
  byte1 +: byte2 +: byte3 +: byte4 +: "".

Local Example encode_char_4_ex1 : encode_char_4 0x1D11E = "𝄞"%string. Proof eq_refl.


Local Definition encode_char (n : N) : option string :=
       if n <?   0x007F then Some (encode_char_1 n)
  else if n <?   0x07FF then Some (encode_char_2 n)
  else if n <?   0xFFFF then Some (encode_char_3 n)
  else if n <? 0x10FFFF then Some (encode_char_4 n)
  else None.

Local Example encode_char_ex1 : encode_char 0x10C8D = Some ("𐲍"%string). Proof eq_refl.


Definition encode_utf8 (u : unicodestring) : option string :=
  let (charcodes) := u                     in
  let append'     := Strings.String.append in
  fold_left (fun a b => option_map2 append' a (encode_char b)) charcodes (Some EmptyString).

Local Example encode_utf8_ex1 : encode_utf8 (Unicode [])                        = Some (      ""%string). Proof eq_refl.
Local Example encode_utf8_ex2 : encode_utf8 (Unicode [52; 50])                  = Some (    "42"%string). Proof eq_refl.
Local Example encode_utf8_ex3 : encode_utf8 (Unicode [961; 32; 0x25B7; 32; 77]) = Some ("ρ ▷ M"%string). Proof eq_refl.


Local Definition decode_char_1 := N_of_ascii.

Local Definition decode_char_2 (a b : ascii) : N :=
  let (y1, y0, x2, x1, x0, _ , _, _) := a in
  let (z3, z2, z1, z0, y3, y2, _, _) := b in
  N_of_digits [z3; z2; z1; z0; y3; y2; y1; y0; x2; x1; x0].

Local Example decode_char_2_ex1 : decode_char_2 (ascii_of_N 207) (ascii_of_N 129) = 961. Proof eq_refl.


Local Definition decode_char_3 (a b c : ascii) : N :=
  let (w3, w2, w1, w0, _ , _ , _, _) := a in
  let (y1, y0, x3, x2, x1, x0, _, _) := b in
  let (z3, z2, z1, z0, y3, y2, _, _) := c in
  N_of_digits [z3; z2; z1; z0; y3; y2; y1; y0; x3; x2; x1; x0; w3; w2; w1; w0].

Local Example decode_char_3_ex1 : decode_char_3 (ascii_of_N 225) (ascii_of_N 143) (ascii_of_N 171) = 0x13EB. Proof eq_refl.


Local Definition decode_char_4 (a b c d : ascii) : N :=
  let (v1, v0, u0, _ , _ , _ , _, _) := a in
  let (w3, w2, w1, w0, v3, v2, _, _) := b in
  let (y1, y0, x3, x2, x1, x0, _, _) := c in
  let (z3, z2, z1, z0, y3, y2, _, _) := d in
  N_of_digits [z3; z2; z1; z0; y3; y2; y1; y0; x3; x2; x1; x0; w3; w2; w1; w0; v3; v2; v1; v0; u0].

Local Example decode_char_4_ex1 : decode_char_4 (ascii_of_N 240) (ascii_of_N 157) (ascii_of_N 132) (ascii_of_N 158) = 0x1D11E. Proof eq_refl.


Local Fixpoint decode_chars (a : string) (acc : list N) (n : nat) {struct n} : option (list N) :=
  let drop n := substring n (length a) a in
  match n, a with
  | S p, String (Ascii _ _ _ _     _     _     _    false) _ => option_flatmap  (decode_char_1 >>    (fun r => decode_chars (drop 1%nat) (r :: acc) p)) (get 0 a)
  | S p, String (Ascii _ _ _ _     _     false true true ) _ => option_flatmap2 (decode_char_2 >>>   (fun r => decode_chars (drop 2%nat) (r :: acc) p)) (get 0 a) (get 1 a)
  | S p, String (Ascii _ _ _ _     false true  true true ) _ => option_flatmap3 (decode_char_3 >>>>  (fun r => decode_chars (drop 3%nat) (r :: acc) p)) (get 0 a) (get 1 a) (get 2 a)
  | S p, String (Ascii _ _ _ false true  true  true true ) _ => option_flatmap4 (decode_char_4 >>>>> (fun r => decode_chars (drop 4%nat) (r :: acc) p)) (get 0 a) (get 1 a) (get 2 a) (get 3 a)
  | _,   EmptyString                                         => Some (rev acc)
  | _,   _                                                   => None
  end.


Definition decode_utf8 (s : string) : option unicodestring :=
  option_map (fun u => Unicode u) (decode_chars s [] (length s)).

Local Example decode_utf8_ex1 : decode_utf8 "𐲍"%string = Some (Unicode [0x10C8D]). Proof eq_refl.
