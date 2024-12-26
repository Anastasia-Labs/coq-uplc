
From CoqUplc Require Import PlutusV3.Uplc.

Set Boolean Equality Schemes.

Inductive expectedBuiltinArg : Set := ArgV | ArgQ.

Inductive expectedBuiltinArgs : Set :=
  | One  : expectedBuiltinArg                        -> expectedBuiltinArgs
  | More : expectedBuiltinArg -> expectedBuiltinArgs -> expectedBuiltinArgs.

Module ExpectedArgNotations.
  Declare Scope expectedArgs_scope.
  Delimit Scope expectedArgs_scope with expected_args.
  
  Notation "'a' [ x ]" := (One x)    (at level 99) : expectedArgs_scope.
  Notation "x ⊙ y"     := (More x y) (at level 99, right associativity) : expectedArgs_scope.
End ExpectedArgNotations.

Import ExpectedArgNotations.
Local Open Scope expectedArgs_scope.

Definition expected_args (b : builtinFun) : expectedBuiltinArgs :=
  match b with
  | AddInteger                      => ArgV ⊙ One ArgV
  | SubtractInteger                 => ArgV ⊙ One ArgV
  | MultiplyInteger                 => ArgV ⊙ One ArgV
  | DivideInteger                   => ArgV ⊙ One ArgV
  | QuotientInteger                 => ArgV ⊙ One ArgV
  | RemainderInteger                => ArgV ⊙ One ArgV
  | ModInteger                      => ArgV ⊙ One ArgV
  | EqualsInteger                   => ArgV ⊙ One ArgV
  | LessThanInteger                 => ArgV ⊙ One ArgV
  | LessThanEqualsInteger           => ArgV ⊙ One ArgV
  | AppendByteString                => ArgV ⊙ One ArgV
  | ConsByteString                  => ArgV ⊙ One ArgV
  | SliceByteString                 => ArgV ⊙ ArgV ⊙ One ArgV
  | LengthOfByteString              => One ArgV
  | IndexByteString                 => ArgV ⊙ One ArgV
  | EqualsByteString                => ArgV ⊙ One ArgV
  | LessThanByteString              => ArgV ⊙ One ArgV
  | LessThanEqualsByteString        => ArgV ⊙ One ArgV
  | Sha2_256                        => One ArgV
  | Sha3_256                        => One ArgV
  | Blake2b_256                     => One ArgV
  | VerifyEd25519Signature          => ArgV ⊙ ArgV ⊙ One ArgV
  | AppendString                    => ArgV ⊙ One ArgV
  | EqualsString                    => ArgV ⊙ One ArgV
  | EncodeUtf8                      => One ArgV
  | DecodeUtf8                      => One ArgV
  | IfThenElse                      => ArgQ ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | ChooseUnit                      => ArgQ ⊙ ArgV ⊙ One ArgV
  | Trace                           => ArgQ ⊙ ArgV ⊙ One ArgV
  | FstPair                         => ArgQ ⊙ ArgQ ⊙ One ArgV
  | SndPair                         => ArgQ ⊙ ArgQ ⊙ One ArgV
  | ChooseList                      => ArgQ ⊙ ArgQ ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | MkCons                          => ArgQ ⊙ ArgV ⊙ One ArgV
  | HeadList                        => ArgQ ⊙ One ArgV
  | TailList                        => ArgQ ⊙ One ArgV
  | NullList                        => ArgQ ⊙ One ArgV
  | ChooseData                      => ArgQ ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ ArgV ⊙ One ArgV
  | ConstrData                      => ArgV ⊙ One ArgV
  | MapData                         => One ArgV
  | ListData                        => One ArgV
  | IData                           => One ArgV
  | BData                           => One ArgV
  | UnConstrData                    => One ArgV
  | UnMapData                       => One ArgV
  | UnListData                      => One ArgV
  | UnIData                         => One ArgV
  | UnBData                         => One ArgV
  | EqualsData                      => ArgV ⊙ One ArgV
  | MkPairData                      => ArgV ⊙ One ArgV
  | MkNilData                       => One ArgV
  | MkNilPairData                   => One ArgV
  | SerializeData                   => One ArgV
  | VerifyEcdsaSecp256k1Signature   => ArgV ⊙ ArgV ⊙ One ArgV
  | VerifySchnorrSecp256k1Signature => ArgV ⊙ ArgV ⊙ One ArgV
  | Bls12_381_G1_add                => ArgV ⊙ One ArgV
  | Bls12_381_G1_neg                => One ArgV
  | Bls12_381_G1_scalarMul          => ArgV ⊙ One ArgV
  | Bls12_381_G1_equal              => ArgV ⊙ One ArgV
  | Bls12_381_G1_hashToGroup        => ArgV ⊙ One ArgV
  | Bls12_381_G1_compress           => One ArgV
  | Bls12_381_G1_uncompress         => One ArgV
  | Bls12_381_G2_add                => ArgV ⊙ One ArgV
  | Bls12_381_G2_neg                => One ArgV
  | Bls12_381_G2_scalarMul          => ArgV ⊙ One ArgV
  | Bls12_381_G2_equal              => ArgV ⊙ One ArgV
  | Bls12_381_G2_hashToGroup        => ArgV ⊙ One ArgV
  | Bls12_381_G2_compress           => One ArgV
  | Bls12_381_G2_uncompress         => One ArgV
  | Bls12_381_millerLoop            => ArgV ⊙ One ArgV
  | Bls12_381_mulMlResult           => ArgV ⊙ One ArgV
  | Bls12_381_finalVerify           => ArgV ⊙ One ArgV
  | Keccak_256                      => ArgV ⊙ One ArgV
  | Blake2b_224                     => ArgV ⊙ One ArgV
  | IntegerToByteString             => ArgV ⊙ ArgV ⊙ One ArgV
  | ByteStringToInteger             => ArgV ⊙ One ArgV
  end.

Module BuiltinNotations.
  Declare Scope builtin_scope.
  Delimit Scope builtin_scope with builtin.

  Notation "'α' ( b )" := (expected_args b) : builtin_scope.
End BuiltinNotations.
