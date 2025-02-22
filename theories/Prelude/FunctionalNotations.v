
Declare Scope functional_scope.
Delimit Scope functional_scope with functional.

Notation "x |> y"    := (y x)                          (at level 94, left associativity, only parsing) : functional_scope.
Notation "x >> y"    := (fun a       => y (x a))       (at level 94, left associativity, only parsing) : functional_scope.
Notation "x >>> y"   := (fun a b     => y (x a b))     (at level 94, left associativity, only parsing) : functional_scope.
Notation "x >>>> y"  := (fun a b c   => y (x a b c))   (at level 94, left associativity, only parsing) : functional_scope.
Notation "x >>>>> y" := (fun a b c d => y (x a b c d)) (at level 94, left associativity, only parsing) : functional_scope.
