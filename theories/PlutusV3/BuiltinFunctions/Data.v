From Coq Require Import Lists.List.
                 Import ListNotations.

From CoqUplc Require Import Prelude.FunctionalNotations.

From CoqUplc Require Import Cbor.Encoding.
From CoqUplc Require Import PlutusV3.CekValue.
From CoqUplc Require Import PlutusV3.Uplc.

Local Open Scope functional_scope.

Definition chooseData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (DataConstr _ _)); c; _; _; _; _] => Some c
  | [VCon (Data (Map        _  )); _; m; _; _; _] => Some m
  | [VCon (Data (DataList   _  )); _; _; l; _; _] => Some l
  | [VCon (Data (I          _  )); _; _; _; i; _] => Some i
  | [VCon (Data (B          _  )); _; _; _; _; b] => Some b
  | _                                             => None
  end.

Local Fixpoint list_const_to_list_data (x : list const) {struct x} : option (list data) :=
  match x with
  | (Data d) :: t => option_map (cons d) (list_const_to_list_data t)
  | _        :: _ => None
  | []            => Some []
  end.

Definition constrData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Integer i); VCon (ConstList xs)] => option_map ((DataConstr i) >> cekValue_of_data) (list_const_to_list_data xs)
  | _                                       => None
  end.

Local Fixpoint list_const_to_data_pair (x : list const) {struct x} : option (list (data * data)) :=
  match x with
  | (Pair (Data p1) (Data p2)) :: t => option_map (cons (p1, p2)) (list_const_to_data_pair t)
  | _                          :: _ => None
  | []                              => Some []
  end.

Definition mapData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (ConstList xs)] => option_map (Map >> cekValue_of_data) (list_const_to_data_pair xs)
  | _                     => None
  end.

Definition listData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (ConstList xs)] => option_map (DataList >> cekValue_of_data) (list_const_to_list_data xs)
  | _                     => None
  end.

Definition iData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Integer i)] => I i |> cekValue_of_data |> Some
  | _                  => None
  end.

Definition bData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (ByteString b)] => B b |> cekValue_of_data |> Some
  | _                     => None
  end.

Local Definition list_data_to_list_const (x : list data) : list const := map Data x.

Definition unConstrData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (DataConstr i xs))] => list_data_to_list_const xs |> ConstList |> cekValue_of_pair (Integer i) |> Some
  | _                               => None
  end.

Local Definition data_pair_to_list_const (x : list (data * data)) : list const :=
  map (fun (x : data * data) => let (p1, p2) := x in Pair (Data p1) (Data p2)) x.

Definition unMapData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (Map xs))] => data_pair_to_list_const xs |> cekValue_of_list |> Some
  | _                      => None
  end.

Definition unListData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (DataList xs))] => list_data_to_list_const xs |> cekValue_of_list |> Some
  | _                           => None
  end.

Definition unIData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (I i))] => i |> cekValue_of_integer |> Some
  | _                   => None
  end.

Definition unBData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data (B b))] => b |> cekValue_of_byteString |> Some
  | _                   => None
  end.

Definition equalsData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data d1); VCon (Data d2)] => data_beq d1 d2 |> cekValue_of_boolean |> Some
  | _                                => None
  end.

Definition mkPairData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data d1); VCon (Data d2)] => cekValue_of_pair (Data d1) (Data d2) |> Some
  | _                                => None
  end.

Definition mkNilData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon Unit] => cekValue_of_list [] |> Some
  | _           => None
  end.

Definition mkNilPairData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon Unit] => cekValue_of_list [] |> Some
  | _           => None
  end.

Definition serialiseData (Vs : list cekValue) : option cekValue :=
  match Vs with
  | [VCon (Data d)] => option_map cekValue_of_byteString (encode_data d)
  | _               => None
  end.
