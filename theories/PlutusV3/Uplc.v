From Coq Require Import Bool.Bool.
From Coq Require Import Init.Decimal.
From Coq Require Import Strings.String.
From Coq Require Import ZArith.

Inductive atomicType : Set :=
  | TypeInteger
  | TypeByteString
  | TypeString
  | TypeBool
  | TypeUnit
  | TypeData.

Inductive typeOperator : Set :=
  | TypeList : builtinType -> typeOperator
  | TypePair : builtinType -> typeOperator

with builtinType : Set :=
  | AtomicType   : atomicType   -> builtinType
  | TypeOperator : typeOperator -> builtinType.

Inductive data : Set :=
  | DataConstr : nat -> list data   -> data
  | Map        : list (data * data) -> data
  | DataList   : list data          -> data
  | I          : Z                  -> data
  | B          : string             -> data.

Inductive const : Set :=
  | Integer              : Z              -> const
  | ByteString           : string         -> const
  | String               : string         -> const
  | Unit                 :                   const
  | Bool                 : bool           -> const
  | ConstList            : list const     -> const
  | Pair                 : const -> const -> const
  | Data                 : data           -> const
  | Bls12_381_G1_element :                   const  (* Cannot be serialized/deserialized, abstract constructor *)
  | Bls12_381_G2_element :                   const  (* Cannot be serialized/deserialized, abstract constructor *)
  | Bls12_381_MlResult   :                   const. (* Cannot be serialized/deserialized, abstract constructor *)

Inductive builtinFun : Set :=
  (* - Batch 1 *)
  (* -- Integer *)
  | AddInteger
  | SubtractInteger
  | MultiplyInteger
  | DivideInteger
  | QuotientInteger
  | RemainderInteger
  | ModInteger
  | EqualsInteger
  | LessThanInteger
  | LessThanEqualsInteger
  (* -- Bytestrings *)
  | AppendByteString
  | ConsByteString
  | SliceByteString
  | LengthOfByteString
  | IndexByteString
  | EqualsByteString
  | LessThanByteString
  | LessThanEqualsByteString
  (* -- Cryptography *)
  | Sha2_256
  | Sha3_256
  | Blake2b_256
  | VerifyEd25519Signature
  (* -- Strings *)
  | AppendString
  | EqualsString
  | EncodeUtf8
  | DecodeUtf8
  (* -- Bool *)
  | IfThenElse
  (* -- Unit *)
  | ChooseUnit
  (* -- Tracing *)
  | Trace
  (* -- Pairs *)
  | FstPair
  | SndPair
  (* -- Lists *)
  | ChooseList
  | MkCons
  | HeadList
  | TailList
  | NullList
  (* -- Data *)
  | ChooseData
  | ConstrData
  | MapData
  | ListData
  | IData
  | BData
  | UnConstrData
  | UnMapData
  | UnListData
  | UnIData
  | UnBData
  | EqualsData
  (* -- Misc constructors *)
  | MkPairData
  | MkNilData
  | MkNilPairData
  (* - Batch 2 *)
  | SerializeData
  (* - Batch 3 *)
  | VerifyEcdsaSecp256k1Signature
  | VerifySchnorrSecp256k1Signature
  (* - Batch 4 = Chang *)
  (* -- Bls curve *)
  | Bls12_381_G1_add
  | Bls12_381_G1_neg
  | Bls12_381_G1_scalarMul
  | Bls12_381_G1_equal
  | Bls12_381_G1_hashToGroup
  | Bls12_381_G1_compress
  | Bls12_381_G1_uncompress
  | Bls12_381_G2_add
  | Bls12_381_G2_neg
  | Bls12_381_G2_scalarMul
  | Bls12_381_G2_equal
  | Bls12_381_G2_hashToGroup
  | Bls12_381_G2_compress
  | Bls12_381_G2_uncompress
  | Bls12_381_millerLoop
  | Bls12_381_mulMlResult
  | Bls12_381_finalVerify
  (* -- Cryptography *)
  | Keccak_256
  | Blake2b_224
  | IntegerToByteString
  | ByteStringToInteger.

  (* Not live yet
  (* - Batch 5 *)
  (* -- ByteString *)
  | AndByteString
  | OrByteString
  | XorByteString
  | ComplementByteString
  | ReadBit
  | WriteBits
  | ReplicateByte
  | ShiftByteString
  | RotateByteString
  | CountSetBits
  | FindFirstSetBit
  (* -- Cryptography *)
  | Ripemd_160
  (* - Batch 6 *)
  | ExpModInteger.
  *)

Inductive term : Set :=
  | Var     : string            -> term
  | Const   : const             -> term
  | Builtin : builtinFun        -> term
  | Lam     : string   -> term  -> term
  | Apply   : term     -> term  -> term
  | Delay   : term              -> term
  | Force   : term              -> term
  | Constr  : nat  -> list term -> term
  | Case    : term -> list term -> term
  | Error   : term.

Inductive version : Set :=
  | Version : nat -> nat -> nat -> version.

Inductive program : Set :=
  | Program : version -> term -> program.
