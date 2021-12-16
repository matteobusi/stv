Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.

Module Trg.
  Import Common.
  Import String.
  Open Scope string_scope.
  Open Scope list_scope.
  Open Scope nat_scope.

  (* Useful domains *)
  Definition loc := val.
  Inductive bop := EPlus | EMinus | ETimes.

  Definition reg := nat.
  Definition r__com := 0.
  Definition r__one := 1.
  Definition r__sp := 2.

  (* Target language: has modules and interfaces, but ignores the latter upon call*)
  Inductive j_inst :=
  | JHalt : j_inst
  | JBnz : reg -> bb_label -> bb_label -> j_inst
  | JJmp : bb_label -> j_inst
  | JCall : iu_name -> fun_name -> bb_label -> j_inst
  | JRet : j_inst.

  Inductive c_inst :=
  | CNop : c_inst (* nop *)
  | CConst : val -> reg -> c_inst (* const v r *)
  | CMov : reg -> reg -> c_inst (* mov rs rd *)
  | CLd : reg -> reg -> c_inst (* ld rs rd, reg (rd) = memory(rs) *)
  | CSt : reg -> reg -> c_inst (* st rs rd *)
  | COp : bop -> reg -> reg -> reg -> c_inst. (* op r1 r2 rd *)

  Inductive bblock :=
  | BBlock : bb_label -> list c_inst -> j_inst -> bblock. (* ℓ: ̄ct *)

  Inductive def :=
  | DDef : fun_name -> list bblock -> def. (* define f { ̄b }*)

  Inductive partial : Set :=
  | PModule: list def -> partial. (* module Main : IMain { ̄d } *)

  Inductive ctx : Set :=
  | CModule : iu_name -> int_name -> list def -> ctx -> ctx (* module u : i { ̄d } C *)
  | CHole : ctx.

  Inductive whole : Set :=
  | WModule : iu_name -> int_name -> list def -> whole -> whole (* module u : i { ̄d } W *)
  | WEmpty : whole.

  Fixpoint link (C : ctx) (P : partial) : whole :=
    match (C, P) with
    | (CModule u i dl C', _) => WModule u i dl (link C' P)
    | (CHole, PModule dl) => (WModule "Main" "IMain" dl WEmpty)
    end.

  (* Semantics *)
  Definition memory := loc -> val.
  Definition update_mem (m : memory) (l : loc) (v : val) : memory :=
    fun l' => if Nat.eqb l l' then v else m l'.
  Definition text_bounds := (nat * nat)%type.

  (* let T = (s, e); Is l ∈ [s, e)? *)
  Definition allow_exec T l :=
    match T with
    | (s, e) => s <= l /\ l < e
    end.

  Definition allow_rw T l :=
    match T with
    | (s, e) => l < s /\ e <= l
    end.

  Definition text_map := iu_name -> ((fun_name * bb_label) + buf_name) -> loc.

  Definition reg_file := reg -> val.
  Definition update_rf (R : reg_file) (r : reg) (v : val) :=
    fun r' => if Nat.eqb r r' then v else R r'.  

  Definition program_counter := loc.
  Definition call_stack := list (iu_name * fun_name * program_counter).

  Axiom decode : text_bounds -> memory -> program_counter -> option (c_inst + j_inst).
  Axiom encode : (c_inst + j_inst) -> val.
  Axiom decode_inv_encode : forall T m pc inst, decode T (update_mem m pc (encode inst)) pc = Some inst.
  Axiom encode_inv_decode : forall T m pc inst, decode T m pc = Some inst -> encode inst = m pc.

  Definition configuration :=
    (bool * whole * text_bounds * text_map * iu_name * fun_name * call_stack * memory * reg_file * program_counter)%type.

   (* For simplicity we just assume fixed text_bounds and text_map *)
  Axiom T : text_bounds.
  Axiom M : text_map.

  Fixpoint get_bblock (mem : memory) (cl : list c_inst) (j : j_inst) (l : loc) : memory :=
    (* FIXME: use a fold *)
    match cl with
    | c::cl' => (fun l' => if Nat.eqb l l' then encode (inl c) else get_bblock mem cl' j (l+1) l')
    | nil => (fun l' => if Nat.eqb l l' then encode (inr j) else mem l')
    end.
    

  (* Note that this leaves unspecified parts as data_mem so to allow initialization of data *)
  Definition program_load (W : whole) (data__init : memory) :=
    match W with
    | WModule u i ld W' =>
      List.fold_left
        (fun pmem d => match d with
                    | DDef f bbl =>
                      List.fold_left
                        (fun ppmem bb => match bb with
                                      | BBlock ℓ cl j =>
                                        get_bblock ppmem cl j (M u (inl (f, ℓ))) 
                                      end
                        ) bbl pmem
                    end
        )
        ld data__init
    | WEmpty => data__init
    end.

  Definition reg_load (mem : memory) :=
    fun r => if Nat.eqb r r__com then mem (M "Main" (inr "arg")) else 0.

  (* Note the first element of the tuple set to true and the dummy values for memory and registers*)
  Definition initial_cfg (W : whole) : configuration :=
    (true, W, T, M, "Main", "main", nil, program_load W (fun _ => 0), (fun _ => 0), M "Main" (inl ("main", "entry"))).
  
  Definition eval_bop op v1 v2 :=
    match op with
    | EPlus => (v1 + v2)
    | EMinus => (v1 - v2)
    | ETimes => (v1 * v2)
    end.

  Inductive eval : configuration -> configuration -> Prop :=
  | SSFirst : forall icfg W T M mem__dummy reg__dummy pc data__init mem__init reg__init,
      icfg = initial_cfg W /\
      icfg = (true, W, T, M, "Main", "main", nil, mem__dummy, reg__dummy, pc) /\
      mem__init = program_load W data__init /\
      reg__init = reg_load mem__init ->
      eval icfg (false, W, T, M, "Main", "main", nil, mem__init, reg__init, pc)
  | SSConst : forall W T M pc c r u f ς m R,
      allow_exec T pc /\
      decode T m pc = Some (inl (CConst c r)) ->
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, update_rf R r c, Nat.succ pc)
  | SSMov : forall W T M pc rs rd rsv u f ς m R,
      allow_exec T pc /\
      decode T m pc = Some (inl (CMov rs rd)) /\
      R rs = rsv ->
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, update_rf R rd rsv, Nat.succ pc)
  | SSLd : forall W T M pc rs rsv rd u f ς m R,
      allow_exec T pc /\
      decode T m pc = Some (inl (CLd rs rd)) /\
      allow_rw T (R rs) /\
      m (R rs) = rsv ->
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, update_rf R rd rsv, Nat.succ pc)
  | SSSt : forall W T M pc rs rsv rd rdv u f ς m R,
      allow_exec T pc /\
      decode T m pc = Some (inl (CSt rs rd)) /\
      R rd = rdv /\
      allow_rw T rdv /\
      R rs = rsv ->
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, update_mem m rdv rsv, R, Nat.succ pc)
  | SSBop : forall W T M u f ς m R pc bop r1 r2 rd v,
      allow_exec T pc /\
      decode T m pc = Some (inl (COp bop r1 r2 rd)) /\
      v = eval_bop bop (R r1) (R r2) ->
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, update_rf R rd v, Nat.succ pc)
  | SSBnzTrue : forall W T M u f ς m R pc r ℓt ℓf new_pc,
      allow_exec T pc /\
      decode T m pc = Some (inr (JBnz r ℓt ℓf)) /\
      R r <> 0 /\ (* cond. is true, jumping to ℓt *)
      M u (inl (f, ℓt)) = new_pc /\
      allow_exec T new_pc -> (* check that the dest address is executable *)
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, R, new_pc)
  | SSBnzFalse : forall W T M u f ς m R pc r ℓt ℓf new_pc,
      allow_exec T pc /\
      decode T m pc = Some (inr (JBnz r ℓt ℓf)) /\
      R r = 0 /\ (* cond. is false, jumping to ℓf *)
      M u (inl (f, ℓf)) = new_pc /\
      allow_exec T new_pc -> (* check that the dest address is executable *)
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, R, new_pc)
  | SSJmp : forall W T M u f ς m R pc ℓ new_pc,
      allow_exec T pc /\
      decode T m pc = Some (inr (JJmp ℓ)) /\
      M u (inl (f, ℓ)) = new_pc /\
      allow_exec T new_pc -> (* check that the dest address is executable *)
      eval (false, W, T, M, u, f, ς, m, R, pc) (false, W, T, M, u, f, ς, m, R, new_pc)
  | SSCall : forall W T M u f__curr ς m R pc u' f ℓr new_pc ret_pc,
      allow_exec T pc /\
      decode T m pc = Some (inr (JCall u' f ℓr)) /\
      M u' (inl (f, "entry")) = new_pc /\
      M u (inl (f__curr, ℓr)) = ret_pc /\
      allow_exec T new_pc -> (* check that the dest address is executable, but !!!no interface checks!!! *)
      eval (false, W, T, M, u, f__curr, ς, m, R, pc) (false, W, T, M, u', f, (u, f__curr, ret_pc)::ς, m, R, new_pc)
  | SSRet : forall W T M u f__curr ς m R pc ret_pc u' f__old,
      allow_exec T pc /\
      decode T m pc = Some (inr JRet) /\
      allow_exec T ret_pc -> 
      eval (false, W, T, M, u, f__curr, (u', f__old, ret_pc)::ς, m, R, pc) (false, W, T, M, u', f__old, ς, m, R, ret_pc).

 (* Now we add observables *)
 Definition get_obs (cfg : configuration) :=
   match cfg with
   | (W, T, M, u, f, ς, m, R, pc) =>
     match decode T m pc with
     | Some (inr (JCall u' f' ℓr)) =>  CFObs.OCall u' f'
     | Some (inr JRet) => CFObs.ORet
     | _ => CFObs.OEmpty
     end
   end.

 Inductive step : configuration -> CFObs.obs -> configuration -> Prop :=
 | SOStep : forall cfg cfg',
              eval cfg cfg' ->
              step cfg (get_obs cfg) cfg'.
End Trg.
