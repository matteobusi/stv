Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.
Require Trg.
Require ATrg.

Module TrgAnalysis.
  Import String.

  Import Common.
  Import Trg.
  Import ATrg.

  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope nat_scope.

  Definition gen_hvar u f ℓ := ATrg.ABBVar ("h_" ++ u ++ "_" ++ f ++ "_" ++ ℓ)%string.

  Definition α__bblock (u : iu_name) (f : fun_name) (bb : Trg.bblock) : ATrg.bblock :=
    match bb with
    | Trg.BBlock ℓ cl Trg.JHalt => ATrg.ABBObs CFObs.OEmpty
    | Trg.BBlock ℓ cl (Trg.JBnz r ℓ1 ℓ2) => ATrg.ABBChoice (gen_hvar u f ℓ1)  (gen_hvar u f ℓ2)
    | Trg.BBlock ℓ cl (Trg.JJmp ℓ') => gen_hvar u f ℓ'
    | Trg.BBlock ℓ cl (Trg.JCall u' f' ℓr) =>
      ATrg.ABBSeq (ATrg.ABBObs (CFObs.OCall u' f')) (ATrg.ABBSeq (gen_hvar u' f' "entry") (gen_hvar u f ℓr))
    | Trg.BBlock ℓ cl (Trg.JRet) => ATrg.ABBObs CFObs.ORet 
    end.


  Definition α__def (u : iu_name) (d : Trg.def) : ATrg.def :=
    match d with
    | Trg.DDef f bbl => ATrg.ADDef f (List.map (fun bb => match bb with Trg.BBlock ℓ cl j => (ℓ, α__bblock u f bb) end) bbl)
    end.

  Definition α__partial (P : Trg.partial) : ATrg.partial :=
    match P with
    | Trg.PModule dl => ATrg.APModule (List.map (fun d => α__def "Main" d) dl)
    end.

  Fixpoint α__ctx (C : Trg.ctx) : ATrg.ctx :=
    match C with
    | Trg.CModule u i dl C' => ATrg.ACModule u i (List.map (fun d => α__def u d) dl) (α__ctx C')
    | Trg.CHole => ATrg.ACHole
    end.

  Fixpoint α__whole (W : Trg.whole) : ATrg.whole :=
    match W with
    | Trg.WModule u i dl W' => ATrg.AWModule u i (List.map (fun d => α__def u d) dl) (α__whole W')
    | Trg.WEmpty => ATrg.AWEmpty
    end.
End TrgAnalysis.
