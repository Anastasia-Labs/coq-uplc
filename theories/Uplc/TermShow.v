From Coq  Require Import Strings.String.

From CoqUplc Require Import Prelude.Show.
From CoqUplc Require Import Unicode.StringShow.

From CoqUplc Require Import Uplc.Term.

Open Scope string_scope.

Instance show_version : Show version := {
  show v :=
    let (n1, n2, n3) := v in "Version " ++ (show n1) ++ " " ++ (show n2) ++ " " ++ (show n3)
}.

Fixpoint showData (d : data) : string :=
  match d with
  | DataConstr i ds => "DataConstr " ++ show i ++ " " ++ showList showData ds
  | Map        ps   => "Map " ++ showList (showPair showData showData) ps
  | DataList   ds   => "DataList " ++ showList showData ds
  | I          i    => "I " ++ show i
  | B          b    => "B " ++ b
  end.

Instance show_data : Show data := {
  show := showData
}.

Fixpoint showConst (c : const) : string :=
  match c with
  | Integer     x         => "Integer " ++ show x
  | ByteString  x         => "ByteString #" ++ x
  | ConstString x         => "ConstString """ ++ show x ++ """"
  | Unit                  => "Unit"
  | Bool        x         => "Bool " ++ show x
  | ConstList   xs        => "ConstList " ++ showList showConst xs
  | Pair        x y       => "Pair (" ++ showConst x ++ ", " ++ showConst y ++ ")"
  | Data        x         => "Data " ++ show x
  | Bls12_381_G1_element  => "Bls12_381_G1_element"
  | Bls12_381_G2_element  => "Bls12_381_G2_element"
  | Bls12_381_MlResult    => "Bls12_381_MlResult"
  end.

Instance show_const : Show const := {
  show := showConst
}.

Instance show_builtinFun : Show builtinFun := {
  show b :=
    match b with
    | AddInteger                      => "AddInteger"
    | SubtractInteger                 => "SubtractInteger"
    | MultiplyInteger                 => "MultiplyInteger"
    | DivideInteger                   => "DivideInteger"
    | QuotientInteger                 => "QuotientInteger"
    | RemainderInteger                => "RemainderInteger"
    | ModInteger                      => "ModInteger"
    | EqualsInteger                   => "EqualsInteger"
    | LessThanInteger                 => "LessThanInteger"
    | LessThanEqualsInteger           => "LessThanEqualsInteger"
    | AppendByteString                => "AppendByteString"
    | ConsByteString                  => "ConsByteString"
    | SliceByteString                 => "SliceByteString"
    | LengthOfByteString              => "LengthOfByteString"
    | IndexByteString                 => "IndexByteString"
    | EqualsByteString                => "EqualsByteString"
    | LessThanByteString              => "LessThanByteString"
    | LessThanEqualsByteString        => "LessThanEqualsByteString"
    | Sha2_256                        => "Sha2_256"
    | Sha3_256                        => "Sha3_256"
    | Blake2b_256                     => "Blake2b_256"
    | VerifyEd25519Signature          => "VerifyEd25519Signature"
    | AppendString                    => "AppendString"
    | EqualsString                    => "EqualsString"
    | EncodeUtf8                      => "EncodeUtf8"
    | DecodeUtf8                      => "DecodeUtf8"
    | IfThenElse                      => "IfThenElse"
    | ChooseUnit                      => "ChooseUnit"
    | Trace                           => "Trace"
    | FstPair                         => "FstPair"
    | SndPair                         => "SndPair"
    | ChooseList                      => "ChooseList"
    | MkCons                          => "MkCons"
    | HeadList                        => "HeadList"
    | TailList                        => "TailList"
    | NullList                        => "NullList"
    | ChooseData                      => "ChooseData"
    | ConstrData                      => "ConstrData"
    | MapData                         => "MapData"
    | ListData                        => "ListData"
    | IData                           => "IData"
    | BData                           => "BData"
    | UnConstrData                    => "UnConstrData"
    | UnMapData                       => "UnMapData"
    | UnListData                      => "UnListData"
    | UnIData                         => "UnIData"
    | UnBData                         => "UnBData"
    | EqualsData                      => "EqualsData"
    | MkPairData                      => "MkPairData"
    | MkNilData                       => "MkNilData"
    | MkNilPairData                   => "MkNilPairData"
    | SerialiseData                   => "SerialiseData"
    | VerifyEcdsaSecp256k1Signature   => "VerifyEcdsaSecp256k1Signature"
    | VerifySchnorrSecp256k1Signature => "VerifySchnorrSecp256k1Signature"
    | Bls12_381_G1_add                => "Bls12_381_G1_add"
    | Bls12_381_G1_neg                => "Bls12_381_G1_neg"
    | Bls12_381_G1_scalarMul          => "Bls12_381_G1_scalarMul"
    | Bls12_381_G1_equal              => "Bls12_381_G1_equal"
    | Bls12_381_G1_hashToGroup        => "Bls12_381_G1_hashToGroup"
    | Bls12_381_G1_compress           => "Bls12_381_G1_compress"
    | Bls12_381_G1_uncompress         => "Bls12_381_G1_uncompress"
    | Bls12_381_G2_add                => "Bls12_381_G2_add"
    | Bls12_381_G2_neg                => "Bls12_381_G2_neg"
    | Bls12_381_G2_scalarMul          => "Bls12_381_G2_scalarMul"
    | Bls12_381_G2_equal              => "Bls12_381_G2_equal"
    | Bls12_381_G2_hashToGroup        => "Bls12_381_G2_hashToGroup"
    | Bls12_381_G2_compress           => "Bls12_381_G2_compress"
    | Bls12_381_G2_uncompress         => "Bls12_381_G2_uncompress"
    | Bls12_381_millerLoop            => "Bls12_381_millerLoop"
    | Bls12_381_mulMlResult           => "Bls12_381_mulMlResult"
    | Bls12_381_finalVerify           => "Bls12_381_finalVerify"
    | Keccak_256                      => "Keccak_256"
    | Blake2b_224                     => "Blake2b_224"
    | IntegerToByteString             => "IntegerToByteString"
    | ByteStringToInteger             => "ByteStringToInteger"
    | AndByteString                   => "AndByteString"
    | OrByteString                    => "OrByteString"
    | XorByteString                   => "XorByteString"
    | ComplementByteString            => "ComplementByteString"
    | ShiftByteString                 => "ShiftByteString"
    | RotateByteString                => "RotateByteString"
    | CountSetBits                    => "CountSetBits"
    | FindFirstSetBit                 => "FindFirstSetBit"
    | ReadBit                         => "ReadBit"
    | WriteBits                       => "WriteBits"
    | ReplicateByte                   => "ReplicateByte"
    | Ripemd_160                      => "Ripemd_160"
    | ExpModInteger                   => "ExpModInteger"
    end
}.

Fixpoint showTerm (t : term) : string :=
  match t with
  | Var              var      => "Var " ++ var
  | Const            c        => "Const (" ++ show c ++ ")"
  | Builtin          b        => "Builtin " ++ show b
  | Lam              var body => "Lam " ++ var ++ "(" ++ showTerm body ++ ")"
  | Apply            f    p   => "Apply (" ++ showTerm f ++ ") (" ++ showTerm p ++ ")"
  | Delay            body     => "Delay (" ++ showTerm body ++ ")"
  | Force            body     => "Force (" ++ showTerm body ++ ")"
  | Constr           i    xs  => "Constr " ++ show i ++ " [" ++ showList showTerm xs ++ "]"
  | Case             t    xs  => "Case (" ++ showTerm t ++ ") [" ++ showList showTerm xs ++ "]"
  | Error                     => "Error"
  end.

Instance show_term : Show term := {
  show := showTerm
}.

Instance show_program : Show program := {
  show p :=
    let (v, body) := p in "Program (" ++ show v ++ ") (" ++ show body ++ ")"
}.
