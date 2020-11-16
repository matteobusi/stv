Require Classical.

Module ClassicUtils.
  Import Classical.
  Lemma contra : forall (P Q : Prop), ((P -> Q) <-> ((not Q) -> (not P))).
    Proof.
      split.
      - intro. eapply imply_to_or in H. destruct H as [Hp | Hq].
        + intro. trivial.
        + intro. eauto.
      - intro. eapply imply_to_or in H. destruct H as [Hq | Hp].
        + apply NNPP in Hq. intro. apply Hq.
        + intro. unfold not in Hp. exfalso. apply Hp. apply H.
    Qed.

    Lemma NNPP_inv : forall (P : Prop), P <-> (not (not P)).
      Proof.
        intros.
        split.
        - intro. unfold not. intro. elim H0. exact H.
        - eapply NNPP.
      Qed.
End ClassicUtils.
 
