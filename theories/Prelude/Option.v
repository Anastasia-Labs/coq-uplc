
Definition option_flatmap {A R : Type} (f : A -> option R) (a' : option A) : option R :=
  match a' with
  | Some a => f a
  | _      => None
  end.

Definition option_flatmap2 {A B R : Type} (f : A -> B -> option R) (a' : option A) (b' : option B) : option R :=
  match a', b' with
  | Some a, Some b => f a b
  | _     , _      => None
  end.

Definition option_flatmap3 {A B C R : Type} (f : A -> B -> C -> option R) (a' : option A) (b' : option B) (c' : option C) : option R :=
  match a', b', c' with
  | Some a, Some b, Some c => f a b c
  | _     , _     , _      => None
  end.

Definition option_flatmap4 {A B C D R : Type} (f : A -> B -> C -> D -> option R) (a' : option A) (b' : option B) (c' : option C) (d' : option D) : option R :=
  match a', b', c', d' with
  | Some a, Some b, Some c, Some d => f a b c d
  | _     , _     , _     , _      => None
  end.

Definition option_map2 {A B R : Type} (f : A -> B -> R) (a' : option A) (b' : option B) : option R :=
  match a', b' with
  | Some a, Some b => Some (f a b)
  | _     , _      => None
  end.
