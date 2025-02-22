From CoqUplc Require Import Prelude.FunctionalNotations.
From CoqUplc Require Import Prelude.List.
From CoqUplc Require Import Prelude.Monad.
                     Import MonadNotations.

From CoqUplc Require Import PlutusV3.CekValue.
From CoqUplc Require Import PlutusV3.Uplc.
From CoqUplc Require Import Unicode.String.

From CoqUplc Require Import PlutusV3.BuiltinFunctions.Bool.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.ByteString.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.Data.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.Integer.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.List.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.Misc.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.Pair.
From CoqUplc Require Import PlutusV3.BuiltinFunctions.String.

Local Open Scope functional_scope.

Definition evaluate_builtin_function (b : builtinFun) : list cekValue -> writer (list unicodestring) (option cekValue) :=
  match b with
  (* -- Integer *)
  | AddInteger               => addInteger               >> mreturn
  | SubtractInteger          => subtractInteger          >> mreturn
  | MultiplyInteger          => multiplyInteger          >> mreturn
  | DivideInteger            => divideInteger            >> mreturn
  | ModInteger               => modInteger               >> mreturn
  | QuotientInteger          => quotientInteger          >> mreturn
  | RemainderInteger         => remainderInteger         >> mreturn
  | EqualsInteger            => equalsInteger            >> mreturn
  | LessThanInteger          => lessThanInteger          >> mreturn
  | LessThanEqualsInteger    => lessThanEqualsInteger    >> mreturn
  (* -- Bytestring *)
  | AppendByteString         => appendByteString         >> mreturn
  | ConsByteString           => consByteString_variant2  >> mreturn (* TODO: verify if it is variant 2 on chain *)
  | SliceByteString          => sliceByteString          >> mreturn
  | LengthOfByteString       => lengthOfByteString       >> mreturn
  | IndexByteString          => indexByteString          >> mreturn
  | EqualsByteString         => equalsByteString         >> mreturn
  | LessThanByteString       => lessThanByteString       >> mreturn
  | LessThanEqualsByteString => lessThanEqualsByteString >> mreturn
  (* -- Cryptography *)
  | Sha2_256                 => fun _ => mreturn None
  | Sha3_256                 => fun _ => mreturn None
  | Blake2b_256              => fun _ => mreturn None
  | VerifyEd25519Signature   => fun _ => mreturn None
  (* -- String *)
  | AppendString             => appendString             >> mreturn
  | EqualsString             => equalsString             >> mreturn
  | EncodeUtf8               => encodeUtf8               >> mreturn
  | DecodeUtf8               => decodeUtf8               >> mreturn
  (* -- Bool *)
  | IfThenElse               => ifThenElse               >> mreturn
  (* -- Misc *)
  | ChooseUnit               => chooseUnit               >> mreturn
  | Trace                    => trace
  (* -- Pair *)
  | FstPair                  => fstPair                  >> mreturn
  | SndPair                  => sndPair                  >> mreturn
  (* -- List *)
  | ChooseList               => chooseList               >> mreturn
  | MkCons                   => mkCons                   >> mreturn
  | HeadList                 => headList                 >> mreturn
  | TailList                 => tailList                 >> mreturn
  | NullList                 => nullList                 >> mreturn
  (* -- Data *)
  | ChooseData               => chooseData               >> mreturn
  | ConstrData               => constrData               >> mreturn
  | MapData                  => mapData                  >> mreturn
  | ListData                 => listData                 >> mreturn
  | IData                    => iData                    >> mreturn
  | BData                    => bData                    >> mreturn
  | UnConstrData             => unConstrData             >> mreturn
  | UnMapData                => unMapData                >> mreturn
  | UnListData               => unListData               >> mreturn
  | UnIData                  => unIData                  >> mreturn
  | UnBData                  => unBData                  >> mreturn
  | EqualsData               => equalsData               >> mreturn
  | MkPairData               => mkPairData               >> mreturn
  | MkNilData                => mkNilData                >> mreturn
  | MkNilPairData            => mkNilPairData            >> mreturn
  | SerialiseData            => serialiseData            >> mreturn
  (* -- Cryptography *)
  | VerifyEcdsaSecp256k1Signature   => fun _ => mreturn None
  | VerifySchnorrSecp256k1Signature => fun _ => mreturn None
  | Bls12_381_G1_add                => fun _ => mreturn None
  | Bls12_381_G1_neg                => fun _ => mreturn None
  | Bls12_381_G1_scalarMul          => fun _ => mreturn None
  | Bls12_381_G1_equal              => fun _ => mreturn None
  | Bls12_381_G1_hashToGroup        => fun _ => mreturn None
  | Bls12_381_G1_compress           => fun _ => mreturn None
  | Bls12_381_G1_uncompress         => fun _ => mreturn None
  | Bls12_381_G2_add                => fun _ => mreturn None
  | Bls12_381_G2_neg                => fun _ => mreturn None
  | Bls12_381_G2_scalarMul          => fun _ => mreturn None
  | Bls12_381_G2_equal              => fun _ => mreturn None
  | Bls12_381_G2_hashToGroup        => fun _ => mreturn None
  | Bls12_381_G2_compress           => fun _ => mreturn None
  | Bls12_381_G2_uncompress         => fun _ => mreturn None
  | Bls12_381_millerLoop            => fun _ => mreturn None
  | Bls12_381_mulMlResult           => fun _ => mreturn None
  | Bls12_381_finalVerify           => fun _ => mreturn None
  | Keccak_256                      => fun _ => mreturn None
  | Blake2b_224                     => fun _ => mreturn None
  (* -- ByteString *)
  | IntegerToByteString      => integerToByteString      >> mreturn
  | ByteStringToInteger      => byteStringToInteger      >> mreturn
  | AndByteString            => andByteString            >> mreturn
  | OrByteString             => orByteString             >> mreturn
  | XorByteString            => xorByteString            >> mreturn
  | ComplementByteString     => complementByteString     >> mreturn
  | ShiftByteString          => shiftByteString          >> mreturn
  | RotateByteString         => rotateByteString         >> mreturn
  | CountSetBits             => countSetBits             >> mreturn
  | FindFirstSetBit          => findFirstSetBit          >> mreturn
  | ReadBit                  => readBit                  >> mreturn
  | WriteBits                => writeBits                >> mreturn
  | ReplicateByte            => replicateByte            >> mreturn
  (* -- Cryptography *)
  | Ripemd_160               => fun _ => mreturn None
  (* -- Integer *)
  | ExpModInteger            => expModInteger            >> mreturn
  end.
