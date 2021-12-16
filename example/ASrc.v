Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.
Require Src.

Module ASrc.
  Import Common.
  Import Src.

  Import String.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope nat_scope.

  Definition configuration := (nat * Src.configuration)%type.

  (* This encodes in the configuration itself the step limit *)
  Definition initial_cfg k cfg__src : configuration := (k, cfg__src).

  (*
    This uses the step limit and the list of provided initial buffers to define
    the testing as a wrapper around the semantics of Src.
   *)
  Inductive step (TestList : list (Src.buf_contents)) : configuration -> CFObs.obs -> configuration -> Prop :=
  | SOFirst : forall cfg k Δ u bc σ K e cfg', (* This wraps the first step of Src *)
      cfg = (Δ, u, None, σ, K, e) /\
      List.In bc TestList /\
      cfg' = (Δ, u, Some bc, σ, K, e) /\
      k > 0 /\
      Src.step cfg (Src.get_obs cfg) cfg'  ->
      step TestList (k, cfg) (Src.get_obs cfg) (k-1, cfg')
  | SONext : forall cfg k s Δ u σ K e cfg', (* Other cases *)
      s <> None /\
      cfg = (Δ, u, s, σ, K, e) /\
      k > 0 /\
      Src.step cfg (Src.get_obs cfg) cfg'  ->
      step TestList (k, cfg) (Src.get_obs cfg) (k-1, cfg').
End ASrc.
