Require List.
Require Streams.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

(** This module defines the minimal framework for STV
    in the case of finite traces and some of its basic properties *)
Module Framework.
  Import List.
  Import Streams.

  Import Classical_Prop.
  Import Classical_Pred_Type.

  Import ClassicUtils.ClassicUtils.

  (** Observables *)
  Axiom obs : Set.

  (** Traces are finite sequences of observables *)
  Definition fin_trace := list obs.
  Definition inf_trace := Stream obs.
  Definition trace := sum fin_trace inf_trace.
  Definition ϵ : trace := inl nil.

  Fixpoint prefix_of (ms : fin_trace) (ts : trace) : Prop :=
    match ms, ts with
    | nil, ts => True
    | m::ms, inl (t::ts) => (eq m t) /\ prefix_of ms (inl ts)
    | m::ms, inr (Cons t ts) => (eq m t) /\ prefix_of ms (inr ts)
    | _, ϵ => False
    end.

  Notation "m ≤ t" := (prefix_of m t) (at level 70, no associativity).

  Lemma t_prefix_t : forall (t : fin_trace), t ≤ (inl t).
  Proof.
    intros t.
    induction t.
    - simpl. trivial.
    - simpl. split. trivial. apply IHt.
  Qed.

  Definition prop : Type := trace -> Prop.

  Check prop.

  (** Base definitions *)
  Record language :=
    {
      (* aux : Set; *)
      whole : Set;
      partial : Set;
      ctx : Set;
      link : ctx -> partial -> whole;
      (* sem : aux -> whole -> obs -> whole -> Prop; transition relation : A ⊢ W -- o --> W' *)
      sem : whole -> obs -> whole -> Prop; (* transition relation : W -- o --> W' *)
    }.

  Notation "C [ P ] : l" := (link l C P) (at level 50).

  (*
    No aux information for now...

    Inductive semstar { l : language } : (aux l -> whole l -> trace -> whole l -> Prop) :=
    | semstar_refl : forall A (W : whole l), semstar A W ϵ W
    | semstar_step : forall A (W W' W'' : whole l) (o : obs) (t : fin_trace),
        sem l A W o W' ->
        semstar A W' (inl t) W'' ->
        semstar A W (inl (o::t)) W''. *)


  Inductive semstar { l : language } : (whole l -> trace -> whole l -> Prop) :=
  | semstar_refl : forall (W : whole l), semstar W ϵ W
  | semstar_step : forall (W W' W'' : whole l) (o : obs) (t : fin_trace),
      sem l W o W' ->
      semstar W' (inl t) W'' ->
      semstar W (inl (o::t)) W''.


  (* Definition beh { l : language } (W : whole l) (t : trace) : Prop := exists A (W' : whole l), semstar A W t W'. *)
  Definition beh { l : language } (W : whole l) (t : trace) : Prop := exists (W' : whole l), semstar W t W'.
  Definition sat { l : language } (W : whole l) (π : prop) := forall t, (beh W t) -> (π t).
  Definition nsat { l : language } (W : whole l) (π : prop) := not (sat W π).

  (** Robust safety property preservation principle (RSP) *)
  Definition safety (π : prop) := forall t, not(π t) -> (exists m, m ≤ t /\ (forall t', m ≤ t' -> not(π t'))).

  Definition RSP {src trg : language} (comp : partial src -> partial trg) : Prop := forall π, (safety π) -> (forall S, (forall C__S, sat (C__S[S] : src) π) -> (forall C__T, sat (C__T[comp S] : trg) π)).
  Definition RSP' {src trg : language} (comp : partial src -> partial trg) : Prop := (forall π, (safety π) -> (forall S C__T, (nsat (C__T[comp S] : trg) π) -> (exists C__S, nsat (C__S[S] : src) π))).
  Definition RSC {src trg : language} (comp : partial src -> partial trg) : Prop := forall S C__T t, (beh (C__T[comp S] : trg) t) -> (forall m, (m ≤ t) -> (exists C__S t', beh (C__S[S] : src) t' /\ m ≤ t')).

  Lemma RSP_contra : (forall src trg (comp : partial src -> partial trg), RSP comp <-> RSP' comp).
  Proof.
    unfold RSP'.
    split.
    all: unfold RSP. intros. eapply imply_to_or in H. destruct H as [Hs | Hp].
    - all: unfold not in Hs. elim Hs. eapply H0.
    - intros. specialize (Hp S). rewrite contra in Hp. eapply not_all_ex_not in Hp.
      + apply Hp.
      + intro. specialize (H C__T). apply H1. exact H.
    - intros. specialize (H π H0 S C__T). rewrite contra in H. unfold nsat in H. apply NNPP in H.
      + apply H.
      + eapply all_not_not_ex. intros. rewrite <- NNPP_inv. eapply H1.
  Qed.

  Theorem RSC_iff_RSP : (forall src trg (comp : partial src -> partial trg), RSC comp <-> RSP comp).
  Proof.
    split.
    - unfold RSC.
      rewrite RSP_contra.
      unfold RSP'.
      intros rsc π Sf S C__T nsat__T.
      unfold nsat in nsat__T. unfold sat in nsat__T. eapply not_all_ex_not in nsat__T.
      destruct nsat__T as [t nbeh__T].
      eapply imply_to_and in nbeh__T.
      destruct nbeh__T as [beh__T nπ].
      destruct (Sf t nπ) as [m [pre H]].
      destruct (rsc S C__T t beh__T m pre) as [C__S [t' [beh__S pre']]].
      unfold nsat. unfold sat.
      exists C__S.
      eapply ex_not_not_all.
      specialize (H t' pre').
      eauto.
    - unfold RSC.
      rewrite RSP_contra.
      unfold RSP'.
      intros rsp' S C__T t beh__T m pre.
      unfold nsat in rsp'. unfold sat in rsp'.
      assert (s : safety (fun b => not (m ≤ b))).
      + unfold safety. intros t0 npre. apply NNPP in npre. exists m. split.
        * assumption.
        * intros t' pre'. rewrite <- NNPP_inv. assumption.
      + specialize (rsp' (fun b => not (m ≤ b)) s S C__T). destruct rsp' as [C__S H0].
        * apply ex_not_not_all. exists t. unfold not. intros H. apply H in beh__T. all: assumption.
        * apply not_all_ex_not in H0. destruct H0 as [t' H1].
          unfold not in H1. apply imply_to_and in H1. destruct H1 as [beh__S npre]. eapply NNPP in npre.
          exists C__S, t'. eauto.
  Qed.

  (** Classical STV: Show abstract RSC and get it in the concrete. *)

  (** Now we lay the basis for our Secure Translation Validation Approach. *)
  Definition STV_RSP {l l' : language} (C__T : ctx l') (S : partial l) (T : partial l') : Prop := forall π, (safety π) -> (forall C__S, sat (C__S[S] : l) π) -> (sat (C__T[T] : l') π).
  Definition STV_RSP' {l l' : language} (C__T : ctx l') (S : partial l) (T : partial l') := (forall π, (safety π) -> (nsat (C__T[T] : l') π -> (exists C__S, nsat (C__S[S] : l) π))).
  Definition STV_RSC {l l' : language} (C__T : ctx l') (S : partial l) (T : partial l') : Prop := (forall t, (beh (C__T[T] : l') t) -> (forall m, (m ≤ t) -> (exists bt t', beh ((bt C__T)[S] : l) t' /\ m ≤ t'))).

  Theorem STV_RSP_iff_RSP : forall (src : language) (trg : language) (comp : partial src -> partial trg), (forall C__T S, STV_RSP C__T S (comp S)) <-> RSP comp.
  Proof.
    unfold STV_RSP. unfold RSP.
    split.
    - intros stv π Sπ S sat__S C__T. apply (stv C__T S π Sπ sat__S).
    - intros rsp C__T S π Sπ sat__S. apply (rsp π Sπ S sat__S C__T).
  Qed.

  Lemma STV_RSP_contra : forall (src : language) (trg : language) (C__T : ctx trg) (S : partial src) (T : partial trg), STV_RSP C__T S T <-> STV_RSP' C__T S T.
  Proof.
    unfold STV_RSP. unfold STV_RSP'.
    intros trg src.
    split.
    - intros rsp π Sπ nsat__T. specialize (rsp π Sπ). rewrite -> contra in rsp. eapply rsp in nsat__T. apply not_all_ex_not in nsat__T. assumption.
    - intros rsp' π Sπ. rewrite -> contra. intro nsat__T. apply ex_not_not_all. specialize (rsp' π Sπ nsat__T). assumption.
  Qed.

  Theorem STV_RSC_iff_STV_RSP : forall (src : language) (trg : language) (C__T : ctx trg) (S : partial src) (T : partial trg), STV_RSC C__T S T <-> STV_RSP C__T S T.
  Proof.
    unfold STV_RSC.
    split.
    - intro rsc.
      apply STV_RSP_contra.
      unfold STV_RSP'.
      intros π Sπ nsat__T.
      unfold nsat in nsat__T. unfold sat in nsat__T.
      apply not_all_ex_not in nsat__T.
      destruct nsat__T as [t nbeh__T]. eapply imply_to_and in nbeh__T. destruct nbeh__T as [beh__T nπ].
      destruct (Sπ t nπ) as [m [pre H0]].
      specialize (rsc t beh__T m pre). destruct rsc as [bt [t' [beh__S' pre']]].
      unfold nsat. unfold sat.
      exists (bt C__T).
      apply ex_not_not_all.
      exists t'.
      unfold not.
      intro beh__S.
      eapply beh__S in beh__S'.
      specialize (H0 t').
      eapply H0 in pre'.
      contradiction.
    - rewrite -> STV_RSP_contra.
      intros rsp' t beh__T m pre.
      unfold STV_RSP' in rsp'.
      assert (s : safety (fun b => not (m ≤ b))).
      + unfold safety. intros t0 npre. apply NNPP in npre. exists m. split.
        * assumption.
        * intros t' pre'. rewrite <- NNPP_inv. assumption.
      + specialize (rsp' (fun b => not (m ≤ b)) s). destruct rsp' as [C__S H0].
        * apply ex_not_not_all. exists t. unfold not. intros H. apply H in beh__T. all: assumption.
        * apply not_all_ex_not in H0. destruct H0 as [t' H1].
          unfold not in H1. apply imply_to_and in H1. destruct H1 as [beh__S npre]. eapply NNPP in npre.
          exists (fun _ => C__S), t'. eauto.
  Qed.

  (** Now we define our notion of STV analysis and prove that it entails STV_RSP *)
  Class analysis (l l' : language) :=
    {
      (* Specification of the analysis *)
      apar : partial l -> partial l';
      actx : ctx l -> ctx l';
      awhole : whole l -> whole l';
    }.

  (* An analysis may be: *)
  Definition llinear {l l' : language} (α : analysis l l') : Prop := forall C P t, (beh (awhole (C[P] : l)) t) <-> (beh ((actx C) [(apar P)] : l') t).
  Definition sound {l l' : language} (α : analysis l l') : Prop := forall C P t, (beh (C[P] : l) t -> beh (awhole (C[P] : l)) t).
  Definition complete {l l' : language} (α : analysis l l') : Prop := forall C P t, (beh (awhole (C[P] : l)) t -> beh (C[P] : l) t).

  (**
     Keep in mind that the typical application of is this is a JIT compiler situation, which also needs to be fast.

     FIRST PRINCIPLE: the naturally arising principle of abstract STV, however -- depending on the usage -- a family of abstract STV_RSC principles may be more useful.
   *)
  Definition aSTV_RSC {src trg asrc atrg : language}
             (α__S : analysis src asrc) (α__T : analysis trg atrg)
             (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop :=
    forall t, (beh ((actx C__T) [apar T] : atrg) t -> (exists bt, beh ((actx (bt C__T)) [apar S] : asrc) t)).

  (** The following results allow us to state that establishing aSTV_RSC is enough for establishing STV_RSC (and thus STV_RSP) *)
  Theorem aSTV_RSC_then_STV_RSC :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T /\ llinear α__S ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC α__S α__T C__T S T -> STV_RSC C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T [sndα [cmpα [lin__T lin__S]]] C__T S T arsc t beh__T m pre.
    specialize (arsc t).
    rewrite <- (lin__T C__T T t) in arsc.
    apply sndα in beh__T.
    eapply arsc in beh__T.
    destruct beh__T as [bt abeh__S].
    rewrite <- (lin__S (bt C__T) S t) in abeh__S.
    apply cmpα in abeh__S.
    exists bt, t.
    split.
    all: assumption.
  Qed.

  Corollary aSTV_RSC_then_STV_RSP :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T /\ llinear α__S ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC α__S α__T C__T S T -> STV_RSP C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T H__α C__T S T arsc. apply aSTV_RSC_then_STV_RSC, (STV_RSC_iff_STV_RSP src trg C__T S T) in arsc. all: assumption.
  Qed.

  (** Obs: the backtranslation of aSTV_RSC may use a specific trace of the behavior to build the source context.
      This may be unwanted (intuitively, one may not know such a trace before execution or don't want to use it for perf. reasons),
      thus we define the Trace Independent variant:
   *)
  Definition aSTV_RSC__TI {src trg asrc atrg : language}
             (α__S : analysis src asrc) (α__T : analysis trg atrg)
             (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop :=
    exists bt, (forall t, (beh ((actx C__T) [apar T] : atrg) t -> beh ((actx (bt C__T)) [apar S] : asrc) t)).

  (* This tactic allows to prove that a given a principle a stronger one can be achieved by making bt independent from t *)
  Ltac bti_then_bt := intros src asrc trg atrg α__S α__T C__T S T H t abeh__T; destruct H as [bt H]; apply H in abeh__T; exists bt; assumption.

  Theorem aSTV_RSC__TI_then_aSTV_RSC : forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
                                         (α__S : analysis src asrc) (α__T : analysis trg atrg) (* Analyses *)
                                         (C__T : ctx trg) (S : partial src) (T : partial trg),
      aSTV_RSC__TI α__S α__T C__T S T -> aSTV_RSC α__S α__T C__T S T.

  Proof.
    bti_then_bt.
  Qed.

  (* Trivially *)
  Corollary aSTV_RSC__TI_then_STV_RSC :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T /\ llinear α__S ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__TI α__S α__T C__T S T -> STV_RSC C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T H__α C__T S T H__TI.
    apply aSTV_RSC__TI_then_aSTV_RSC, (aSTV_RSC_then_STV_RSC src asrc trg atrg α__S α__T H__α) in H__TI.
    assumption.
  Qed.

  (**
     SECOND PRINCIPLE: the requirements for the complete source analysis to be (1) usable on source contexts alone (2) linear, are quite strong: think about testing at source level.
     The following principle (Whole Non-linear Source Analysis) is useful when the two requirements above don't hold, and the program loader has access to both the source program and the target context must be manipulated directly at load time!

Of course, it can be made stronger by moving bt out of the forall t quantifier (TIWNSA).

     Example usage: JIT compiler, tests at source, sound analysis at target.
   *)
  Definition aSTV_RSC__WNSA {src trg asrc atrg : language}
             (α__S : analysis src asrc) (α__T : analysis trg atrg)
             (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop :=
    (forall t, (beh ((actx C__T) [apar T] : atrg) t -> exists bt, beh (awhole ((bt C__T) [S] : src)) t)).

  (** The following results allow us to state that establishing aSTV_RSC is enough for establishing STV_RSC (and thus STV_RSP) *)
  Theorem aSTV_RSC__WNSA_then_STV_RSC :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__WNSA α__S α__T C__T S T -> STV_RSC C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T [sndα [cmpα lin__T]] C__T S T arsc t beh__T m pre.
    specialize (arsc t).
    rewrite <- (lin__T C__T T t) in arsc.
    apply sndα in beh__T.
    eapply arsc in beh__T.
    destruct beh__T as [bt abeh__S].
    apply cmpα in abeh__S.
    exists bt, t.
    split.
    all: assumption.
  Qed.

  Corollary aSTV_RSC__WNSA_then_STV_RSP :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__WNSA α__S α__T C__T S T -> STV_RSP C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T H__α C__T S T arsc. apply aSTV_RSC__WNSA_then_STV_RSC, (STV_RSC_iff_STV_RSP src trg C__T S T) in arsc. all: assumption.
  Qed.

  (** Again, we can define its Trace Independent variant: *)
  Definition aSTV_RSC__TIWNSA {src trg asrc atrg : language}
             (α__S : analysis src asrc) (α__T : analysis trg atrg)
             (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop :=
    exists bt, (forall t, (beh ((actx C__T) [apar T] : atrg) t -> beh (awhole ((bt C__T) [S] : src)) t)).

  Theorem aSTV_RSC__TIWNSA_then_aSTV_RSC__WNSA : forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
                                         (α__S : analysis src asrc) (α__T : analysis trg atrg) (* Analyses *)
                                         (C__T : ctx trg) (S : partial src) (T : partial trg),
      aSTV_RSC__TIWNSA α__S α__T C__T S T -> aSTV_RSC__WNSA α__S α__T C__T S T.
  Proof. bti_then_bt. Qed.

  (* Trivially *)
  Corollary aSTV_RSC__TIWNSA_then_STV_RSC :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__T ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__TIWNSA α__S α__T C__T S T -> STV_RSC C__T S T)).
  Proof.
    intros src asrc trg atrg α__S α__T H__α C__T S T H__TI.
    apply aSTV_RSC__TIWNSA_then_aSTV_RSC__WNSA, (aSTV_RSC__WNSA_then_STV_RSC src asrc trg atrg α__S α__T H__α) in H__TI.
    assumption.
  Qed.

  (* Also the following holds: *)
  Theorem aSTV_RSC__WNSA_then_aSTV_RSC :
    forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *)
      (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *)
      (sound α__T /\ complete α__S /\ llinear α__S /\ llinear α__T ->
       (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__WNSA α__S α__T C__T S T <-> aSTV_RSC α__S α__T C__T S T)).
  Proof.
    unfold aSTV_RSC__WNSA, aSTV_RSC.
    intros src asrc trg atrg α__S α__T H__α C__T S T.
    split.
    - intros H__WNSA t beh__T. destruct (H__WNSA t beh__T) as [bt beh__btT]. exists bt. apply H__α. assumption.
    - intros H__RSC t beh__T. destruct (H__RSC t beh__T) as [bt beh__btT]. exists bt. apply H__α. assumption.
  Qed.

  (* ====================== DEPRECATED IN FAVOR OF THE PREVIOUS PRINCIPLE *)
  (*
  (*    The following principle (Back Translation on Abstract target context) is useful when linearity holds at the source, but the program loader has no access to the target concrete context (e.g., for performance reasons)! *)

  (*    Of course, it can be made stronger by moving bt out of the forall t quantifier (TIBTA). *)

  (*    Example usage: JIT compiler, complete analysis at source, sound analysis at target. *)
  (*  *) *)
  (* Definition aSTV_RSC__BTA {src trg asrc atrg : language} *)
  (*            (α__S : analysis src asrc) (α__T : analysis trg atrg) *)
  (*            (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop := *)
  (*   (forall t, (beh ((actx C__T) [apar T] : atrg) t -> exists bt, beh ((bt (actx C__T))[apar S] : asrc) t)). *)

  (* (** The following results allow us to state that establishing aSTV_RSC is enough for establishing STV_RSC (and thus STV_RSP) *) *)
  (* Theorem aSTV_RSC__BTA_then_STV_RSC : *)
  (*   forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *) *)
  (*     (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *) *)
  (*     (sound α__T /\ complete α__S /\  llinear α__S /\ llinear α__T -> *)
  (*      (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__BTA α__S α__T C__T S T -> STV_RSC C__T S T)). *)
  (* Proof. *)
  (*   intros src asrc trg atrg α__S α__T [sndα [cmpα [lin__S lin__T]]] C__T S T arsc t beh__T m pre. *)

  (*   specialize (arsc t). *)
  (*   rewrite <- (lin__T C__T T t) in arsc. *)
  (*   apply sndα in beh__T. *)
  (*   eapply arsc in beh__T. *)
  (*   destruct beh__T as [bt abeh__S]. *)
  (*   exists bt. *)
  (* Admitted. *)

  (* Corollary aSTV_RSC__BTA_then_STV_RSP : *)
  (*   forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *) *)
  (*     (α__S : analysis src asrc) (α__T : analysis trg atrg), (* Analyses *) *)
  (*     (sound α__T /\ complete α__S /\ llinear α__S /\ llinear α__T -> *)
  (*      (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__BTA α__S α__T C__T S T -> STV_RSP C__T S T)). *)
  (* Proof. *)
  (*   intros src asrc trg atrg α__S α__T H__α C__T S T arsc. apply aSTV_RSC__BTA_then_STV_RSC, (STV_RSC_iff_STV_RSP src trg C__T S T) in arsc. all: assumption. *)
  (* Qed. *)

  (* (** Again, we can define its Trace Independent variant: *) *)
  (* Definition aSTV_RSC__TIBTA {src trg asrc atrg : language} *)
  (*            (α_S : analysis src asrc) (α_T : analysis trg atrg) *)
  (*            (C__T : ctx trg) (S : partial src) (T : partial trg) : Prop := *)
  (*   exists bt, (forall t, (beh ((actx C__T) [apar T] : atrg) t -> beh ((bt (actx C__T))[apar S] : asrc) t)). *)

  (* Theorem aSTV_RSC__TIBTA_then_aSTV_RSC__BTA : forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *) *)
  (*                                        (α_S : analysis src asrc) (α_T : analysis trg atrg) (* Analyses *) *)
  (*                                        (C__T : ctx trg) (S : partial src) (T : partial trg), *)
  (*     aSTV_RSC__TIBTA α_S α_T C__T S T -> aSTV_RSC__BTA α_S α_T C__T S T. *)
  (* Proof. bti_then_bt. Qed. *)

  (* (* Trivially *) *)
  (* Corollary aSTV_RSC__TIBTA_then_STV_RSC : *)
  (*   forall (src : language) (asrc : language) (trg : language) (atrg : language) (* Languages used *) *)
  (*     (α_S : analysis src asrc) (α_T : analysis trg atrg), (* Analyses *) *)
  (*     (sound α_T /\ complete α_S /\ llinear α_S /\ llinear α_T -> *)
  (*      (forall (C__T : ctx trg) (S : partial src) (T : partial trg), aSTV_RSC__TIBTA α_S α_T C__T S T -> STV_RSC C__T S T)). *)
  (* Proof. *)
  (*   intros src asrc trg atrg α_S α_T H__α C__T S T H__TI. *)
  (*   apply aSTV_RSC__TIBTA_then_aSTV_RSC__BTA, (aSTV_RSC__BTA_then_STV_RSC src asrc trg atrg α_S α_T H__α) in H__TI. *)
  (*   assumption. *)
  (* Qed. *)


  (** Finally, we can write our secure translation validation algorithm and prove it correct *)
  (* Inductive STV_RESULT := MAYBE_UNSAFE | SAFE. *)

  (* Require Import Coq.Logic.Decidable. *)
  (* Axiom deceq : decidable (). *)

  (** This is pseudo-code for a possibile STV algorithm. *)
  (*
        fun safe_to_run (C__T : ctx trg) (aS : partial asrc) (aT : partial trg) :=
            if beh ((actx C__T)[aT] : atrg) <= beh ((actx (bt C__T))[aS] : asrc) then
               (SAFE, ⊥)
            else
               (MAYBE_UNSAFE, bt C__T)
  *)

End Framework.

