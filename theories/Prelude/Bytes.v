From Coq Require Import FunInd.
From Coq Require Import funind.Recdef.
From Coq Require Import Lists.List.
                 Import ListNotations.
From Coq Require Import Strings.Ascii.
From Coq Require Import Strings.String.
From Coq Require Import NArith.
From Coq Require Import ZArith.

From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.Option.

Local Open Scope functional_scope.
Local Open Scope positive_scope.

Local Fixpoint bit_list_of_pos_le (p : positive) {struct p} : list bool :=
  match p with
  | p ~ 1 => true  :: bit_list_of_pos_le p
  | p ~ 0 => false :: bit_list_of_pos_le p
  | xH    => [true]
  end.

Local Example bit_list_of_pos_le_ex1 : bit_list_of_pos_le 15 = [ true; true;  true; true]. Proof eq_refl.
Local Example bit_list_of_pos_le_ex2 : bit_list_of_pos_le 10 = [false; true; false; true]. Proof eq_refl.


Local Definition bytestring_of_pos_le (p : positive) : string :=
  let bit_list_le := bit_list_of_pos_le p in
  (fix loop (l : list bool) {struct l} : string :=
    match l with
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t => String (Ascii b0 b1    b2    b3    b4    b5    b6    b7   ) (loop t)
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil     => String (Ascii b0 b1    b2    b3    b4    b5    b6    false) EmptyString
    | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil           => String (Ascii b0 b1    b2    b3    b4    b5    false false) EmptyString
    | b0 :: b1 :: b2 :: b3 :: b4 :: nil                 => String (Ascii b0 b1    b2    b3    b4    false false false) EmptyString
    | b0 :: b1 :: b2 :: b3 :: nil                       => String (Ascii b0 b1    b2    b3    false false false false) EmptyString
    | b0 :: b1 :: b2 :: nil                             => String (Ascii b0 b1    b2    false false false false false) EmptyString
    | b0 :: b1 :: nil                                   => String (Ascii b0 b1    false false false false false false) EmptyString
    | b0 :: nil                                         => String (Ascii b0 false false false false false false false) EmptyString
    | nil                                               => EmptyString
    end) bit_list_le.

Local Example bytestring_of_pos_le_ex1 : bytestring_of_pos_le   15 = string_of_list_ascii ["015"%char].             Proof eq_refl.
Local Example bytestring_of_pos_le_ex2 : bytestring_of_pos_le 1234 = string_of_list_ascii ["210"%char; "004"%char]. Proof eq_refl.


Definition bytestring_of_N_le (n : N) : string :=
  match n with
  | N0     => ""%string
  | Npos p => bytestring_of_pos_le p
  end.

Definition bytestring_of_N_be (n : N) : string := n |> bytestring_of_N_le |> list_ascii_of_string |> @rev ascii |> string_of_list_ascii.


Local Open Scope Z_scope.
Local Open Scope bool_scope.

Local Fixpoint replicate (a : ascii) (n : nat) : string :=
  match n with
  | O   => EmptyString
  | S p => String a (replicate a p)
  end.

Local Definition pad_string_left (s : string) (w : nat) : string :=
  concat "" [replicate "000"%char (w - length s); s].

Local Definition pad_string_right (s : string) (w : nat) : string :=
  concat "" [s; replicate "000"%char (w - length s)].

Local Example pad_string_left_ex  : pad_string_left  "12"%string 4 = string_of_list_ascii ["000"%char; "000"%char; "1"%char; "2"%char]. Proof eq_refl.
Local Example pad_string_rigth_ex : pad_string_right "12"%string 4 = string_of_list_ascii ["1"%char; "2"%char; "000"%char; "000"%char]. Proof eq_refl.

Definition integer_to_bytestring (e : bool) (w n : Z) : option string :=
  let w_in_range := (0 <=? w) && (w <=? 8192       ) in
  let n_in_range := (0 <=? n) && (n <?  Z.pow 256 w) in
  match w_in_range && n_in_range, e with
  | true , true  => (* big-endian *)
      let bs := n |> Z.to_N |> bytestring_of_N_be in
      if w =? 0 then Some bs
                else Some (pad_string_left bs (w |> Z.to_nat))
  | true , false => (* little-endian *)
      let bs := n |> Z.to_N |> bytestring_of_N_le in
      if w =? 0 then Some bs
                else Some (pad_string_right bs (w |> Z.to_nat))
  | false, _     => None
  end.


Fixpoint bytestring_to_integer_le (s : string) {struct s} : N :=
  match s with
  | EmptyString => 0
  | String a t  => (N_of_ascii a) + 256 * (bytestring_to_integer_le t)
  end.

Local Example bytestring_to_integer_le_ex1 : bytestring_to_integer_le "cafe"%string = 1701208419%N. Proof eq_refl.

Fixpoint bytestring_to_integer_be (s : string) (acc : N) {struct s} : N :=
  match s with
  | EmptyString => acc
  | String a t  => bytestring_to_integer_be t ((N_of_ascii a) + acc * 256)
  end.

Local Example bytestring_to_integer_be_ex1 : bytestring_to_integer_be "efac"%string 0 = 1701208419%N. Proof eq_refl.

Definition bytestring_to_integer (e : bool) (s : string) : N :=
  match e with
  | true  => bytestring_to_integer_be s 0
  | false => bytestring_to_integer_le s
  end.


Local Close Scope Z_scope.
Local Close Scope positive_scope.

Definition truncate_to (s : string) (k : nat)             : string := substring 0 k s.
Definition extend_to   (s : string) (k : nat) (a : ascii) : string := append s (replicate a (k - length s)).

Local Definition and_ascii (a b : ascii) : ascii :=
  let (a0, a1, a2, a3, a4, a5, a6, a7) := a in
  let (b0, b1, b2, b3, b4, b5, b6, b7) := b in
  Ascii (andb a0 b0) (andb a1 b1) (andb a2 b2) (andb a3 b3) (andb a4 b4) (andb a5 b5) (andb a6 b6) (andb a7 b7).

Local Definition or_ascii (a b : ascii) : ascii :=
  let (a0, a1, a2, a3, a4, a5, a6, a7) := a in
  let (b0, b1, b2, b3, b4, b5, b6, b7) := b in
  Ascii (orb a0 b0) (orb a1 b1) (orb a2 b2) (orb a3 b3) (orb a4 b4) (orb a5 b5) (orb a6 b6) (orb a7 b7).

Local Definition xor_ascii (a b : ascii) : ascii :=
  let (a0, a1, a2, a3, a4, a5, a6, a7) := a in
  let (b0, b1, b2, b3, b4, b5, b6, b7) := b in
  Ascii (xorb a0 b0) (xorb a1 b1) (xorb a2 b2) (xorb a3 b3) (xorb a4 b4) (xorb a5 b5) (xorb a6 b6) (xorb a7 b7).

Local Fixpoint string_map2 (f : ascii -> ascii -> ascii) (s1 s2 : string) {struct s1} : string :=
  match s1, s2 with
  | EmptyString  , _             => EmptyString
  | _            , EmptyString   => EmptyString
  | String a1 s1', String a2 s2' => String (f a1 a2) (string_map2 f s1' s2')
  end.

Local Definition loop_over_strings (f : ascii -> ascii -> ascii) (e : bool) (a : ascii) (s1 s2 : string) : string :=
  match e with
  | false => let l := Nat.min (length s1) (length s2) in string_map2 f (truncate_to s1 l) (truncate_to s2 l)
  | true  => let l := Nat.max (length s1) (length s2) in string_map2 f (extend_to s1 l a) (extend_to s2 l a)
  end.

Definition and_bytestring (e : bool) (s1 s2 : string) : string := loop_over_strings and_ascii e "255"%char s1 s2.
Definition  or_bytestring (e : bool) (s1 s2 : string) : string := loop_over_strings or_ascii  e "000"%char s1 s2.
Definition xor_bytestring (e : bool) (s1 s2 : string) : string := loop_over_strings xor_ascii e "000"%char s1 s2.


Local Fixpoint bytestring_to_bits (s : string) {struct s} : list bool :=
  match s with
  | String (Ascii b0 b1 b2 b3 b4 b5 b6 b7) t => b7 :: b6 :: b5 :: b4 :: b3 :: b2 :: b1 :: b0 :: bytestring_to_bits t
  | EmptyString                              => []
  end.

Local Example bytestring_to_bits_ex1 : bytestring_to_bits " "%string = [false; false; true; false; false; false; false; false]. Proof eq_refl.

Local Fixpoint bytestring_of_bits (l : list bool) : string :=
  match l with
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: t => String (Ascii b7    b6    b5    b4    b3    b2    b1    b0   ) (bytestring_of_bits t)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil     => String (Ascii b6    b5    b4    b3    b2    b1    b0    false) EmptyString
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: nil           => String (Ascii b5    b4    b3    b2    b1    b0    false false) EmptyString
  | b0 :: b1 :: b2 :: b3 :: b4 :: nil                 => String (Ascii b4    b3    b2    b1    b0    false false false) EmptyString
  | b0 :: b1 :: b2 :: b3 :: nil                       => String (Ascii b3    b2    b1    b0    false false false false) EmptyString
  | b0 :: b1 :: b2 :: nil                             => String (Ascii b2    b1    b0    false false false false false) EmptyString
  | b0 :: b1 :: nil                                   => String (Ascii b1    b0    false false false false false false) EmptyString
  | b0 :: nil                                         => String (Ascii b0    false false false false false false false) EmptyString
  | nil                                               => EmptyString
  end.

Local Example bytestring_of_bits_ex1 : bytestring_of_bits [true; false; false; false; false; false] = " "%string. Proof eq_refl.

Local Theorem bytestring_bits_bytestring : forall s, (s |> bytestring_to_bits |> bytestring_of_bits) = s.
Proof.
  induction s as [|a t IHs].
  - reflexivity.
  - destruct a as [b0 b1 b2 b3 b4 b5 b6 b7] eqn: Ea; simpl; repeat rewrite <- Ea; now rewrite IHs.
Qed.


Definition shift_bits_left (s : string) (k : nat) : string :=
  let b  := bytestring_to_bits s            in
  let b' := skipn k (b ++ (repeat false k)) in
  bytestring_of_bits b'.

(* "ca" = x63 x61 = 0110 0011  0110 0001 *)
(*        xC6 xC2 = 1100 0110  1100 0010 *)
Local Example shift_bits_left_ex1 : shift_bits_left "ca"%string  1 = string_of_list_ascii ["198"%char; "194"%char]. Proof eq_refl.
Local Example shift_bits_left_ex2 : shift_bits_left "ca"%string  8 = string_of_list_ascii [  "a"%char; "000"%char]. Proof eq_refl.
Local Example shift_bits_left_ex3 : shift_bits_left "ca"%string 16 = string_of_list_ascii ["000"%char; "000"%char]. Proof eq_refl.
Local Example shift_bits_left_ex4 : shift_bits_left   ""%string 24 = ""%string. Proof eq_refl.

Definition shift_bits_right (s : string) (k : nat) : string :=
  let b  := bytestring_to_bits s                           in
  let b' := firstn (List.length b) ((repeat false k) ++ b) in
  bytestring_of_bits b'.

(* "ca" = x63 x61 = 0110 0011  0110 0001 *)
(*        x31 xB0 = 0011 0001  1011 0000 *)
Local Example shift_bits_right_ex1 : shift_bits_right "ca"%string  1 = string_of_list_ascii ["049"%char; "176"%char]. Proof eq_refl.
Local Example shift_bits_right_ex2 : shift_bits_right "ca"%string  8 = string_of_list_ascii ["000"%char;   "c"%char]. Proof eq_refl.
Local Example shift_bits_right_ex3 : shift_bits_right "ca"%string 16 = string_of_list_ascii ["000"%char; "000"%char]. Proof eq_refl.
Local Example shift_bits_right_ex4 : shift_bits_right   ""%string  2 = ""%string. Proof eq_refl.

Definition rotate_bits_left (s : string) (k : nat) : string :=
  let b  := bytestring_to_bits s          in
  let k' := Nat.modulo k (List.length b)  in
  let b' := skipn k' (b ++ (firstn k' b)) in
  bytestring_of_bits b'.

(* "ca" = x63 x61 = 0110 0011  0110 0001 *)
(*        xC6 xC2 = 1100 0110  1100 0010 *)
Local Example rotate_bits_left_ex1 : rotate_bits_left "ca"%string  1 = string_of_list_ascii ["198"%char; "194"%char]. Proof eq_refl.
Local Example rotate_bits_left_ex2 : rotate_bits_left "ca"%string  8 = "ac"%string. Proof eq_refl.
Local Example rotate_bits_left_ex3 : rotate_bits_left "ca"%string 16 = "ca"%string. Proof eq_refl.
Local Example rotate_bits_left_ex4 : rotate_bits_left "ca"%string 24 = "ac"%string. Proof eq_refl.
Local Example rotate_bits_left_ex5 : rotate_bits_left   ""%string 32 =  ""%string. Proof eq_refl.

Definition rotate_bits_right (s : string) (k : nat) : string :=
  let b  := bytestring_to_bits s                      in
  let k' := Nat.modulo k (List.length b)              in
  let n  := List.length b - k'                        in
  let b' := firstn (List.length b) ((skipn n b) ++ b) in
  bytestring_of_bits b'.

(* "ca" = x63 x61 = 0110 0011  0110 0001 *)
(*        xB1 xB0 = 1011 0001  1011 0000 *)
Local Example rotate_bits_right_ex1 : rotate_bits_right "ca"%string  1 = string_of_list_ascii ["177"%char; "176"%char]. Proof eq_refl.
Local Example rotate_bits_right_ex2 : rotate_bits_right "ca"%string  8 = "ac"%string. Proof eq_refl.
Local Example rotate_bits_right_ex3 : rotate_bits_right "ca"%string 16 = "ca"%string. Proof eq_refl.
Local Example rotate_bits_right_ex4 : rotate_bits_right "ca"%string 24 = "ac"%string. Proof eq_refl.
Local Example rotate_bits_right_ex5 : rotate_bits_right   ""%string  7 =   ""%string. Proof eq_refl.

Definition count_set_bits (s : string) : nat := count_occ Bool.bool_dec (bytestring_to_bits s) true.

Local Fixpoint find_index {A : Type} (f : A -> bool) (l : list A) : option nat :=
  match l with
  | h :: t => if f h then Some 0 else option_map (Nat.add 1) (find_index f t)
  | []     => None
  end.

Definition first_set_bit (s : string) : Z :=
  match find_index id (s |> bytestring_to_bits |> @rev bool) with
  | Some x => x |> Z.of_nat
  | None   => -1
  end.

Local Example first_set_bit_ex1 : first_set_bit " "%string = 5%Z. Proof eq_refl.

Definition read_bit (s : string) (n : nat) : option bool :=
  let b := (s |> bytestring_to_bits |> @rev bool) in
  nth_error b n.

Local Example read_bit_ex1 : read_bit " "%string 5 = Some true. Proof eq_refl.


Local Fixpoint update_bit (b : list bool) (n : nat) (u : bool) {struct b} : option (list bool) :=
  match b, n with
  | h :: t, 0   => Some (u :: t)
  | h :: t, S p => option_map (cons h) (update_bit t p u)
  | []    , _   => None
  end.

Local Example update_bit_ex1 : update_bit [true; true; true; true] 2 false = Some [true; true; false; true]. Proof eq_refl.

Local Theorem update_bits_spec1 : forall b n u, n < List.length b -> update_bit b n u = Some (firstn n b ++ [u] ++ skipn (n + 1) b).
Proof.
  induction b as [|h t IHb].
  - simpl; intros n u Hn; contradict Hn; unfold lt; apply Nat.nle_succ_0. 
  - induction n as [|p IHp]; try reflexivity; simpl; intros u HSp; rewrite IHb.
    + reflexivity.
    + now apply PeanoNat.lt_S_n.
Qed.

Local Theorem update_bits_spec2 : forall b n u, List.length b <= n -> update_bit b n u = None.
Proof.
  induction b as [|h t IHb]; try reflexivity; induction n as [|p IHp]; simpl; intros u Hl.
  - contradict Hl; apply Nat.nle_succ_0. 
  - rewrite IHb; [reflexivity | now apply le_S_n].
Qed.

Fixpoint update_bits (j : list Z) (u : bool) (b : list bool) {struct j} : option (list bool) :=
  match j with
  | Zpos p :: t => option_flatmap (update_bits t u) (update_bit b (Pos.to_nat p) u)
  | Z0     :: t => option_flatmap (update_bits t u) (update_bit b 0              u)
  | Zneg _ :: _ => None
  | []          => Some b
  end.

Definition write_bits (s : string) (u : bool) (j : list Z) : option string :=
  let r := update_bits j u (s |> bytestring_to_bits |> @rev bool) in
  option_map (@rev bool >> bytestring_of_bits) r.


Local Open Scope Z_scope.

Definition replicate_bytes (l b : Z) : option string :=
       if (l <? 0) || (8192 <? l) then None
  else if (b <? 0) || ( 255 <? b) then None
  else replicate (b |> Z.to_N |> ascii_of_N) (l |> Z.to_nat) |> Some.
