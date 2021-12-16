Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.

Module Src.
  Import Common.
  Import String.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope nat_scope.

  Definition buf_name := string.

  (* This maps each buffer name to its length -- Local to the component *)
  Definition buf_list := buf_name -> option nat. 

  Definition int_env := int_name -> list fun_name.

  Definition val := nat.
  Inductive bop := EPlus | EMinus | ETimes | ELeq | EEq | ESeq.

  (* Syntax: source language *)
  Inductive expr :=
  | EVal : val -> expr (* value *)
  | EBop : bop -> expr -> expr -> expr (* e₁ ⊗ e₂ *)
  | EIfThenElse : expr -> expr -> expr -> expr (* if e then e₁ else e₂ *)
  | ERead : buf_name -> expr -> expr (* b[e] *)
  | EAssign : buf_name -> expr -> expr -> expr (* b[e] := e *)
  | ECall : iu_name -> fun_name -> expr -> expr (* C.P(e) *)
  | EHalt : expr. (* halt *)

  Inductive decl :=
  | DFun : fun_name -> expr -> decl. (* fun f { e } *)
 
  (* Here we slighly differ from the paper, each compartment defines its own buffer list *)
  Inductive partial : Set :=
  (* IMain is assumed to include just main and declared implicitly *)
  (* buf list of Main + compartment Main : IMain { decl* } *)
  | PCompartment : buf_list -> list decl -> partial.

  Inductive ctx : Set :=
  (* This allows to declare interfaces *)
  | CInterface : int_name -> list fun_name -> ctx -> ctx
  (* buf list of u + compartment u : i { decl* } ... *)
  | CCompartment : iu_name -> int_name -> buf_list -> list decl -> ctx -> ctx
  | CHole : ctx.

  Inductive whole : Set :=
  (* This allows to declare interfaces *)
  | WInterface : int_name -> list fun_name -> whole -> whole
  (* buff list of u + compartment u : i { decl* } ... *)
  | WCompartment : iu_name -> int_name -> buf_list -> list decl -> whole -> whole
  | WEmpty : whole.

  Fixpoint link (C : ctx) (P : partial) : whole :=
    match (C, P) with
    | (CInterface i fl C', _) => WInterface i fl (link C' P)
    | (CCompartment u i bl dl C', _) => WCompartment u i bl dl (link C' P)
    | (CHole, PCompartment bl dl) => (WInterface "IMain" ("main"::nil) (WCompartment "Main" "IMain" bl dl WEmpty))
    end.

  (* Semantics: Function environments and utilities *)
  Inductive fun_body :=
  | FBPub : expr -> fun_body
  | FBPriv : expr -> fun_body
  | FBNone : fun_body.

  Definition fun_env := fun_name -> fun_body.

  (* We setup now Δ ∈ whole_env *)
  Definition env := (int_env * (iu_name -> option buf_list) * (iu_name -> option fun_env))%type.

  Definition build_env (W : whole) : env :=
    let fun_of_decl :=
        (fix fun_of_decl ie i dl :=
           match dl with
           | (DFun f e)::dl' =>
             let pub := (List.existsb (fun f' => eqb f f') (ie i)) in
             (fun f' => (if andb (eqb f f') pub then FBPub e
                      else if andb (eqb f f') (negb pub) then FBPriv e
                           else fun_of_decl ie i dl' f'))
           | nil =>  (fun _ => FBNone)
           end) in
    let build_int_env :=
        (fix build_int_env W := match W with
                                | WInterface i fl W' => (fun i' => if eqb i i' then fl else build_int_env W' i')
                                | WEmpty => (fun i' => nil)
                                | WCompartment u i bl dl W' => build_int_env W'
                                end) in
    let build_fn_bl :=
        (fix build_fn_bl W := match W with
                              | WCompartment u i bl dl W' => (fun u' => (if eqb u u' then Some bl else build_fn_bl W' u'))
                              | WEmpty => (fun _ => None)
                              | WInterface i fl W' => build_fn_bl W'
                              end) in
    let build_fn_fe :=
        (fix build_fn_fe W ie := match W with
                                 | WCompartment u i bl dl W' =>
                                   (fun u' => (if eqb u u' then Some (fun_of_decl ie i dl) else build_fn_fe W' ie u'))
                                 | WEmpty => (fun _ => None)
                                 | WInterface i fl W' => build_fn_fe W' ie
                                 end) in
    let ie := build_int_env W in
    (ie, build_fn_bl W, build_fn_fe W ie).

  (* Semantics: each configuration also includes a function carrying the values of the buffers *)
  Definition buf_contents := iu_name -> buf_name -> nat -> option val.

  Definition initial_bc (Δ : env) : buf_contents :=
    fun u b i => match Δ with
              | (ie, blf, fef) => match blf u with
                                 | Some bl => match bl b with
                                             | Some len =>
                                               if andb (Nat.leb 0 i) (Nat.ltb i len) then Some 0
                                               else None (* This is the out-of-bound case *)
                                             | _ => None (* This is the case in which b is undefined in u *)
                                             end
                                 | _ => None (* This is the case in which u is undefined *)
                                 end
              end.

  Definition update_bc (s : buf_contents) (u : iu_name) (b : buf_name) (i : nat) (v : val) : buf_contents :=
    fun u' b' i' => if andb (eqb u u') (andb (eqb b b') (EqNat.beq_nat i i')) then
                   match (s u b i) with
                   | Some v' => Some v (* Update, only when b in u is defined at idx i *)
                   | _ => None
                   end
                 else s u b i.

  (* Semantics: Continuations *)
  Inductive knt :=
  | KEmpty : knt (* ϵ *)
  | KBopL : bop -> expr -> knt (* ◻ ⊗ e *)
  | KBopR : val -> bop -> knt (* v ⊗ ◻ *)
  | KIfThenElse : expr -> expr -> knt (* if ◻ then e else e *)
  | KRead : buf_name -> knt (* b[◻] *)
  | KAssignL : buf_name -> expr -> knt (* b[◻] := e *)
  | KAssignR : buf_name -> val -> knt (* b[v] := ◻ *)
  | KCall : iu_name -> fun_name -> knt. (* u.f(◻) *)

  Definition continuation := list knt.

  (* Semantics: stacks.
     A stack includes:
       - compartment to return to
       - the old value of the argv buffer
       - old continuation
       - name of function being executed
  *)
  Definition stack := list (iu_name * val * continuation * fun_name). 

  (* Semantics: validity of whole programs and utilities *)
  Fixpoint iu_list (W : whole) : list iu_name :=
    match W with
    | WCompartment u i bl dl W' => u::(iu_list W')
    | WEmpty => nil
    | WInterface i fl W' => iu_list W'
    end.

  Fixpoint fun_list_of_dl (dl : list decl) :=
    match dl with
    | (DFun f e)::dl' => f::(fun_list_of_dl dl')
    | _ => nil
    end.

  Fixpoint fun_list (W: whole) (u : iu_name) : list fun_name :=
    match W with
    | WCompartment u i bl dl W' => (fun_list_of_dl dl) ++ (fun_list W' u)
    | WEmpty => nil
    | WInterface i fl W' => fun_list W' u
    end.

  (*
    A whole program is valid (validity is *NOT* well-typedness!) iff:
    - Main IU exists and Main.main is implemented and public
    - Each IU is defined only once
    - Each IU has an argv buffer of length 1
    - All the functions are defined just once

    By definition, if a program is not valid, then its initial configuration is stuck (see below).
   *)
  Definition whole_valid (W : whole) : Prop :=
    let Δ := build_env W in
    let iul := iu_list W in
    let fl := fun_list W in
    (forall u, List.In u iul -> (* for each defined IU *)
          (forall ie blf fef bl fl, Δ = (ie, blf, fef) /\ blf u = Some bl -> 
                               (
                                 List.count_occ String.string_dec iul u = 1 /\
                                 bl "argv" = Some 1 /\
                                 (forall f, List.In f (fl u) -> List.count_occ String.string_dec (fl u) f = 1)
                               )
          )
    )
    /\
    (exists ie blf fef fe e, Δ = (ie, blf, fef) /\ 
                        fef "Main" = Some fe /\ List.In "Main" iul /\ (* Main IU exists *)
                        fe "main" = FBPub e (* Main.main is implemented and public *)
    ).

  Definition configuration := (env * iu_name * (option buf_contents) * stack * continuation * expr)%type.

  Definition initial_cfg (W : whole) : configuration :=
    let Δ := build_env W in
    match Δ with
    | (ie, blf, fef) => match fef "Main" with
                              | Some fe => match fe "main" with
                                          | FBPub e__main => (Δ, "Main", None, nil, nil, e__main)
                                          | _ => (Δ, "Main", None, nil, nil, EHalt)
                                          end
                              | None => (Δ, "Main", None, nil, nil, EHalt)
                            end
    end.
  
  Definition eval_bop op v1 v2 :=
    match op with
    | EPlus => EVal (v1 + v2)
    | EMinus => EVal (v1 - v2)
    | ETimes => EVal (v1 * v2)
    | ELeq => if Nat.leb v1 v2 then EVal 1 else EVal 0 
    | EEq => if Nat.eqb v1 v2 then EVal 1 else EVal 0
    | ESeq => EVal v2
    end.

  Definition can_call_then_get (fe : fun_env) (from_iu : iu_name) (to_iu : iu_name) (to_f : fun_name) :=
    match fe to_f with
    | FBPriv body => if eqb from_iu to_iu then Some body else None
    | FBPub body => Some body
    | FBNone => None
    end.

  (* Semantics *)
  (*
    A valid program may get stuck when:
       - Halt or Value and empty continuation (graceful termination)
       - Accesses or writes to a non-existing buffer or outside its bounds (premise in SSReadVal and SSAssign)
       - Calls to non-public functions (premise in calls)
  *)
  (* This is the semantics from [CSF'16] with minor changes
     - The most interesting one being SSFirst case:
         + From the initial configuration (buffers set to None),
           we go to any configuration with some initial buffer values (expressed by Some s__init).
   *)
  Inductive eval : configuration -> configuration -> Prop :=
  | SSFirst : forall Δ e__main s__init,
      eval (Δ, "Main", None, nil, nil, e__main) (Δ, "Main", Some s__init, nil, nil, e__main)
  | SSBopL : forall Δ u s σ K op e1 e2,
      eval (Δ, u, s, σ, K, EBop op e1 e2) (Δ, u, s, σ, (KBopL op e2)::K, e1)
  | SSBopR : forall Δ u s σ K op v1 e2,
      eval (Δ, u, s, σ, (KBopL op e2)::K, EVal v1) (Δ, u, s, σ, (KBopR v1 op)::K, e2)
  | SSBopVal : forall Δ u s σ K op v1 v2,
      eval (Δ, u, s, σ, (KBopR v1 op)::K, EVal v2) (Δ, u, s, σ, K, eval_bop op v1 v2)
  | SSITECondition : forall Δ u s σ K e e1 e2,
      eval (Δ, u, s, σ, K, EIfThenElse e e1 e2) (Δ, u, s, σ, (KIfThenElse e1 e2)::K, e)
  | SSITENonZero :  forall Δ u s σ K v e1 e2,
      v <> 0 -> 
      eval (Δ, u, s, σ, (KIfThenElse e1 e2)::K, EVal v) (Δ, u, s, σ, K, e1)
  | SSITEZero :  forall Δ u s σ K e1 e2,
      eval (Δ, u, s, σ, (KIfThenElse e1 e2)::K, EVal 0) (Δ, u, s, σ, K, e2)
  | SSReadIndex : forall Δ u s σ K b e,
      eval (Δ, u, s, σ, K, ERead b e) (Δ, u, s, σ, (KRead b)::K, e)
  | SSReadVal :  forall Δ u s s__actual σ K b i v,
      s = Some s__actual /\
      s__actual u b i = Some v ->
      eval (Δ, u, s, σ, (KRead b)::K, EVal i) (Δ, u, s, σ, K, EVal v)
  | SSAssignIndex : forall Δ u s σ K b e1 e2,
      eval (Δ, u, s, σ, K, EAssign b e1 e2) (Δ, u, s, σ, (KAssignL b e2)::K, e1)
  | SSAssignRHS : forall Δ u s σ K b v1 e2,
      eval (Δ, u, s, σ, (KAssignL b e2)::K, EVal v1) (Δ, u, s, σ, (KAssignR b v1)::K, e2)
  | SSAssign : forall Δ u s s__actual σ K b v1 v2 v,
      s = Some s__actual /\
      s__actual u b v2 = Some v ->
      eval (Δ, u, s, σ, (KAssignR b v1)::K, EVal v2) (Δ, u, Some (update_bc s__actual u b v1 v2), σ, K, EVal v2)
  | SSCallArg : forall Δ u s σ K u' f e,
      eval (Δ, u, s, σ, K, ECall u' f e) (Δ, u, s, σ, (KCall u' f)::K, e)
  | SSCallIntra : forall Δ u s s__actual σ f K v oldv dummy body,
      (* intra-module all calls are permitted*)
      (exists ie blf fef fe, Δ = (ie, blf, fef) /\ (fef u = Some fe) /\ (fe f = FBPub body \/ fe f = FBPriv body)) /\
      s = Some s__actual /\
      s__actual u "argv" 0 = Some dummy /\
      s__actual u "argv" 0 = Some oldv ->
      eval (Δ, u, s, σ, (KCall u f)::K, EVal v) (Δ, u, Some (update_bc s__actual u "argv" 0 v), (u, oldv, K, f)::σ, nil, body)
  | SSCallInter : forall Δ u u' s s__actual σ f K v oldv dummy body,
      (* inter-module calls only to public functions *)
      (exists ie blf fef fe,  Δ = (ie, blf, fef) /\ (fef u' = Some fe) /\ fe f = FBPub body) /\
      s = Some s__actual /\
      s__actual u' "argv" 0 = Some dummy /\
      s__actual u "argv" 0 = Some oldv ->
      eval (Δ, u, s, σ, (KCall u' f)::K, EVal v) (Δ, u', Some (update_bc s__actual u' "argv" 0 v), (u, oldv, K, f)::σ, nil, body)
  | SSRet : forall Δ u s s__actual u' oldv K f σ retv,
      s = Some s__actual ->
      eval (Δ, u, s, (u', oldv, K, f)::σ, nil, EVal retv) (Δ, u', Some (update_bc s__actual u "argv" 0 oldv), σ, K, EVal retv).

 (* Now we add observables *)
 Definition get_obs (cfg : configuration) :=
   match cfg with
   | (_, _, _, _, (KCall u' f)::_, EVal _) => CFObs.OCall u' f
   | (_, _, _, (_, _, _, _)::_, nil, EVal _) => CFObs.ORet
   | _ => CFObs.OEmpty
   end.

 Inductive step : configuration -> CFObs.obs -> configuration -> Prop :=
 | SOStep : forall cfg cfg',
              eval cfg cfg' ->
              step cfg (get_obs cfg) cfg'.
End Src.
