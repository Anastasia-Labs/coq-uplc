From Coq Require Import Init.Byte.
From Coq Require Import Strings.String.

From CoqUplc Require Import Prelude.Show.
From CoqUplc Require Import Unicode.String.
From CoqUplc Require Import Unicode.Utf8Encoding.

Instance show_unicodestring : Show unicodestring := {
  show u :=
    match encode_utf8 u with
    | Some s => "Unicode """ ++ s ++ """"
    | None   => "Unicode: message utf8 encoding error"
    end
}.

Definition parse_unicodestring (x : list byte) : option unicodestring :=
  decode_utf8 (string_of_list_byte x).

Definition print_unicodestring (x : unicodestring) : option (list byte) :=
  option_map (list_byte_of_string) (encode_utf8 x).

Declare Scope unicode_scope.
Delimit Scope unicode_scope with unicode.

String Notation unicodestring parse_unicodestring print_unicodestring : unicode_scope.

