Require Import Framework.
Require Import String.

(* Common domains and names *)
Definition iu_name := string.
Definition int_name := string.
Definition fun_name := string.
Definition val := nat.
Definition buf_name := string.
Definition bb_label := string.

(* Observables *)
Module CFObs <: Obs.
  Inductive _obs :=
  | OCall : iu_name -> fun_name -> _obs
  | ORet
  | OEmpty.

  Definition obs := _obs.
End CFObs.
