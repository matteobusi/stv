Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.

Module ATrg.
  Import String.

  Import Common.

  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope nat_scope.

  (* Useful domains *)
  Definition histvar := string.

  (* Abstract target language: has modules and interfaces *)
  Inductive bblock :=
  | ABBEpsilon : bblock
  | ABBObs : CFObs.obs -> bblock
  | ABBChoice : bblock -> bblock -> bblock
  | ABBSeq : bblock -> bblock -> bblock
  | ABBVar : histvar -> bblock.

  Inductive def :=
  | ADDef : fun_name -> list (bb_label * bblock) -> def. (* (f, (ℓ: β)* ) *)

  Inductive partial : Set :=
  | APModule: list def -> partial. (* Main : IMain { δ* } *)

  Inductive ctx : Set :=
  | ACModule : iu_name -> int_name -> list def -> ctx -> ctx (* u : i { δ* } Γ *)
  | ACHole : ctx.

  Inductive whole : Set :=
  | AWModule : iu_name -> int_name -> list def -> whole -> whole (* u : i { δ* } aW *)
  | AWEmpty : whole.

  Fixpoint link (Γ : ctx) (Π : partial) : whole :=
    match (Γ, Π) with
    | (ACModule u i δl Γ', _) => AWModule u i δl (link Γ' Π)
    | (ACHole, APModule δl) => (AWModule "Main" "IMain" δl AWEmpty)
    end.

  (* Semantics *)
  Definition histvar_env := histvar -> bblock.
  Definition configuration :=
    (histvar_env * bblock)%type.

  (* First, a few axioms *)
  (* (abblock, ABBSeq) is a monoid *)
  Axiom assoc_seq : forall β β' β'', ABBSeq (ABBSeq β β') β'' = ABBSeq β (ABBSeq β' β'').
  Axiom id_seq : forall β, ABBSeq ABBEpsilon β = β /\ ABBSeq β ABBEpsilon = β.

  (* (abblock, ABBChoice) is a commutative monoid *)
  Axiom assoc_choice : forall β β' β'', ABBChoice (ABBChoice β β') β'' = ABBChoice β (ABBChoice β' β'').
  Axiom id_choice : forall β, ABBChoice ABBEpsilon β = β /\ ABBChoice β ABBEpsilon = β.
  Axiom comm_choice : forall β β', ABBChoice β β' = ABBChoice β' β.

  (* Also seq operator distributes over choice *)
  Axiom seq_dist_choice : forall o β β',
      ABBSeq (ABBObs o) (ABBChoice β β') = ABBChoice (ABBSeq (ABBObs o) β) (ABBSeq (ABBObs o) β').

  (*
    Equality here is up to the above axioms!
   *)
  Inductive step : configuration -> CFObs.obs -> configuration -> Prop :=
  | SSObs : forall ρ o,
      step (ρ, ABBObs o) o (ρ, ABBEpsilon)
  | SSEpsSeq : forall ρ β,
      step (ρ, ABBSeq ABBEpsilon β) CFObs.OEmpty (ρ, β)
  | SSSeq : forall ρ o β1 β'1 β2,
      step (ρ, β1) o (ρ, β'1) ->
      step (ρ, ABBSeq β1 β2) o (ρ, ABBSeq β'1 β2)
  | SSHVar : forall ρ h,
      step (ρ, ABBVar h) CFObs.OEmpty (ρ, ρ h)
  | SSChoice : forall ρ β1 β2,
      step (ρ, ABBChoice β1 β2) CFObs.OEmpty (ρ, β1).

  (*
      We assume Λ, a bijection from module names, function names and (if needed) basic block labels to history variable names.
      Note that we do not require modules/functions/labels to be in the whole program, so the requirement of surjectivity is reasonable.
   *)
  Axiom Λ : iu_name -> fun_name -> bb_label -> histvar.
  Axiom Λ__inv : histvar -> (iu_name * fun_name * bb_label).
  Axiom Λ_inv_Λ__inv : (forall u f ℓ, Λ__inv (Λ u f ℓ) = (u, f, ℓ)) /\ (forall h u f ℓ, Λ__inv h = (u, f, ℓ) -> Λ u f ℓ = h).

  (*
    Another thing to define is the environment.
    We assume entry to be the entry point of any functions (as in Trg, LLVM-style)
    So, we assume a variable of the form h_u_f_ℓ to be referred to th ℓ bblock of u.f (entrypoint of f if ℓ = entry)
  *)
  Fixpoint get_bb_ufℓ (W : whole) u f ℓ :=
    match W with
    | AWModule u' i ((ADDef f' ((ℓ', β)::βl))::δl) W' =>
      if andb (eqb ℓ ℓ') (andb (eqb u u') (eqb f f')) then β else get_bb_ufℓ W' u f ℓ
    | _ => ABBEpsilon
    end.

  Definition build_env (W : whole) : histvar_env :=
    (fun h => match Λ__inv h with
          | (u, f, ℓ) => get_bb_ufℓ W u f ℓ
          end).

  Definition initial_cfg (W : whole) : configuration := let ρ := build_env W in (ρ, ρ (Λ "Main" "main" "entry")).
End ATrg.
