Require Import Framework.
Require Import String.
Require Import Common.

Require Import Src.
Require Import Trg.
Require Import ASrc.
Require Import ATrg.

Require Import TrgAnalysis.

Module CFFramework := Framework CFObs.

Module CaseStudy.
  Definition src :=
    CFFramework.Build_language
      Src.configuration (* Whole__S *)
      Src.partial (* Partial__S *)
      Src.ctx (* Context__S *)
      (fun C P => Src.initial_cfg (Src.link C P)) (* Linking *)
      Src.step. (* SOS semantics with observables *)

  Definition trg :=
    CFFramework.Build_language
      Trg.configuration
      Trg.partial
      Trg.ctx
      (fun C P => Trg.initial_cfg (Trg.link C P))
      Trg.step.

  (* The abstract source language is just src with a "testing" semantics *)
  Axiom k : nat. (* The maximum number of steps allowed by testing *)
  Axiom TestList : list Src.buf_contents. (* This is the set of inputs *)

  Definition asrc :=
    CFFramework.Build_language
      ASrc.configuration (* Whole__S *)
      Src.partial (* Partial__S *)
      Src.ctx (* Context__S *)
      (fun C P => ASrc.initial_cfg k (Src.initial_cfg (Src.link C P))) (* Linking *)
      (ASrc.step TestList). (* SOS semantics with observables *)

  (* The source analysis is trivial *)
  Definition α__src :=
    (CFFramework.Build_analysis src asrc)
      (fun P => P)
      (fun C => C)
      (fun W => ASrc.initial_cfg k W).

  (* This proof is done pencil and paper in the attached README.org file *)
  Theorem completeness_α__src : CFFramework.complete α__src.
  Proof. Admitted.

  (* The abstract target language is that of history expressions *)
  Definition atrg :=
    CFFramework.Build_language
      ATrg.configuration
      ATrg.partial
      ATrg.ctx
      (fun C P => ATrg.initial_cfg (ATrg.link C P))
      ATrg.step.

  (* The source analysis is a simple type and effect system *)

  Definition trgwhole_of_config (cfg : Trg.configuration) :=
    match cfg with
    | (b, W, T, M, u, f, ς, m, R, pc) => W
    end.

  Definition α__trg :=
    (CFFramework.Build_analysis trg atrg)
      TrgAnalysis.α__partial
      TrgAnalysis.α__ctx
      (fun trgcfg => ATrg.initial_cfg (TrgAnalysis.α__whole (trgwhole_of_config trgcfg))).

  (* This proof is done pencil and paper in the attached README.org file *)
  Theorem linearity_α__trg : CFFramework.llinear α__trg.
  Proof. Admitted.

  Theorem soundness_α__trg : CFFramework.sound α__trg.
  Proof. Admitted.
End CaseStudy.
