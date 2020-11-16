(**
   This is the source language for our use case.
   This is taken from MinCaml abstract syntax and adapted to our framework.
 *)
Require Int63.
Require PrimFloat.
Require List.
Require String.


Require Framework.


Module Source.
  Import Int63.
  Import PrimFloat.
  Import List.
  Import String.

  Import Framework.

  Definition SId : Set := string.
  Inductive SType : Set := 
  | STUnit
  | STBool
  | STInt
  | STFloat
  | STFun : list SType -> SType -> SType (* arguments are uncurried *)
  | Tuple : list SType -> SType
  | Array : SType -> SType
  | Var : SType -> SType.

  Record SFunDecl : Set :=
    {
      name : SId * SType;
      args : list (SId * SType);
    }.

  Inductive Par__S : Set :=
  (** Primitives *)
  | SPrim : SId -> Par__S
  (** Values *)
  | SUnit
  | STrue | SFalse
  | SInt : int -> Par__S
  | SFloat : float -> Par__S
  (** Boolean ops *)
  | SNot : Par__S -> Par__S
  (** (Int) Arithmetic ops *)
  | SNeg : Par__S -> Par__S
  | SAdd : Par__S -> Par__S -> Par__S
  | SSub : Par__S -> Par__S -> Par__S
  (** (Float) Arithmetic ops *)
  | SFNeg : Par__S -> Par__S
  | SFAdd : Par__S -> Par__S -> Par__S
  | SFSub : Par__S -> Par__S -> Par__S
  | SFMul : Par__S -> Par__S -> Par__S
  | SFDiv : Par__S -> Par__S -> Par__S
  (** Comparison and conditionals *)
  | SEq : Par__S -> Par__S -> Par__S
  | SLE : Par__S -> Par__S -> Par__S
  | SIf : Par__S -> Par__S -> Par__S -> Par__S
  (** Names and bindings *)
  | SLet : (SId * SType) -> Par__S -> Par__S -> Par__S
  | SVar : SId -> Par__S
  | SLetRec : SFunDecl -> Par__S -> Par__S -> Par__S
  (** Application *)
  | SApp : Par__S -> list Par__S -> Par__S
  (** Tuples *)
  | STuple : list Par__S -> Par__S
  | SLetTuple : list (SId * SType) -> Par__S -> Par__S -> Par__S
  (** Arrays *)
  | SArray : Par__S -> Par__S -> Par__S
  | SGet : Par__S -> Par__S -> Par__S
  | SPut : Par__S -> Par__S -> Par__S -> Par__S.

  Inductive Ctx__S : Set :=
  | CSHole
  | CSLet : (SId * SType) -> Par__S -> Ctx__S -> Ctx__S
  | CSLetRec : SFunDecl -> Par__S -> Ctx__S -> Ctx__S.

  Fixpoint link__S C S := match C with
                               | CSHole => S
                               | CSLet (x, τ) S' C' => SLet (x, τ) S' (link__S C' S)
                               | CSLetRec f S' C' => SLetRec f S' (link__S C' S)
                        end.

  Definition Whole__S := Par__S. (* : Set := { W | exists C S, W = link__S C S }. *)

  Inductive Obs : Set :=
  | OEmp
  | OPrim : SId -> Obs (* Call to primitive  *)
  | OCall : SId -> Obs (* Function calls *)
  | ORet : SId -> Obs. (* Function returns *)

  Inductive sem__S : Whole__S -> Obs -> Whole__S -> Prop := 
  | SSNot0 : sem__S (SNot STrue) OEmp SFalse | SNot1 : sem__S (SNot SFalse) OEmp STrue
  | SSNot2 : forall S o S', sem__S S o S' -> sem__S (SNot S) o (SNot S')
  | SSNeg0 : forall n, sem__S (SNeg (SInt n)) OEmp (SNeg (SInt (-n)))
  | SSNeg1 : forall S o S', sem__S S o S' -> sem__S (SNeg S) o (SNot S').

  Check Framework.obs.
  Check Obs.

  Definition Lang := Framework.Build_language Whole__S Par__S Ctx__S link__S sem__S.
End Source.
