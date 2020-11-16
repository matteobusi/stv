

(**
   This is the source language for our use case.
   This is taken from ICFP paper on KreMLin, Sec. 3.1
 *)
Require Int63.
Require List.
Require String.
Require Coq.Program.Tactics.
Require Coq.Program.Wf.


Require Framework.

Module LowStar.
  Import Int63.
  Import List.
  Import String.

  Import Framework.

  Open Scope int63_scope.
  Open Scope string_scope.
  Open Scope list_scope.
  Import ListNotations.

  Definition Id__LS := string. (* Identifiers *)
  Definition FId__LS : Set := string. (* Field names *)
  Definition AId__LS : Set := string. (* Abstract types names *)
  Definition BufAddr__LS : Set := int.
  Definition BufOff__LS : Set := int.

  (** Fig. 4 of ICFP'17 by Protzenko et al. *)
  Inductive Type__LS : Set := (* τ *)
  | LTUnit
  | LTInt
  | LTRec : list (FId__LS * Type__LS) -> Type__LS (* Records: { f0 = τ0, ..., fn = τn } *)
  | LTBuf : Type__LS -> Type__LS (* Typed buffers *)
  | LTAbs : AId__LS ->  Type__LS.

  (** A bit more liberal than Figg. 4 and 13 of ICFP'17 by Protzenko et al. *)
  Inductive Val__LS := (* v *)
  | LVUnit 
  | LVVar : Id__LS -> Val__LS
  | LVInt : int -> Val__LS
  | LVRec : list (FId__LS * Val__LS) -> Val__LS
  | LVMut : BufAddr__LS -> BufOff__LS -> list FId__LS -> Val__LS.

  Inductive Exp__LS : Set := (* e *)
  | LRBuf : (Id__LS * Type__LS) -> (Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let x = readbuf e1 e2 in e *)
  | LWBuf : (Exp__LS * Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let _ = writebuf e1 e2 e3 in e *)  
  | LNBuf : Id__LS -> BufOff__LS -> (Exp__LS * Type__LS) -> Exp__LS -> Exp__LS (* let x = newbuf n (e1 : τ) in e *)
  | LSubbuf : Exp__LS -> Exp__LS -> Exp__LS (* subbuf e1 e2 *)
  | LRStruct : (Id__LS * Type__LS) -> Exp__LS -> Exp__LS -> Exp__LS (* Let x : τ = readstruct e1 in e *)
  | LWStruct : (Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let _ = writestruct e1 e2 in e *)  
  | LNStruct : Id__LS -> (Exp__LS * Type__LS) -> Exp__LS -> Exp__LS (* let x = newstruct (e1 : τ) in e *)
  | LMProj : Exp__LS -> FId__LS -> Exp__LS (* e ▷ f *)
  | LWith : Exp__LS -> Exp__LS (* withframe e *)
  | LPop : Exp__LS -> Exp__LS (* pop e *)
  | LIfThenElse : Exp__LS -> Exp__LS -> Exp__LS -> Exp__LS (* if e1 then e2 else e3 *)
  | LApp : (Id__LS * Type__LS) -> (Id__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let x : τ = fn e1 in e *)
  | LLet : (Id__LS * Type__LS) -> Exp__LS -> Exp__LS -> Exp__LS (* let x : τ = e1 in e *)
  | LRec : list (FId__LS * Exp__LS) -> Exp__LS (* { f0 = e0, ..., fn = en } *)
  | LIProj : Exp__LS -> FId__LS -> Exp__LS (* e.f *)
  | LVal : Val__LS -> Exp__LS. (* v *)

  Definition Fun__LS : Set := ((Id__LS * Type__LS) * (Exp__LS * Type__LS)).

  Coercion LVVar : Id__LS >-> Val__LS.
  Coercion LVInt : int >-> Val__LS.
  Coercion LVal : Val__LS >-> Exp__LS.
  
  Inductive Prog__LS : Set :=
  | PLNil 
  | PLLet : (Id__LS * Type__LS) -> Val__LS -> Prog__LS -> Prog__LS (* let x : τ = e1 in Prog *)
  | PLLetFun : Id__LS -> Fun__LS -> Prog__LS -> Prog__LS. (* let x = λ (y : τ). (e1 : τ) in S *)

  Fixpoint getDef (D : Prog__LS) (x : Id__LS) : option (Fun__LS + Val__LS) :=
    match D with
    | PLNil => None
    | PLLet (y, _) e1 D' => if string_dec x y then Some (inr e1) else getDef D' x (* y ≠ x *)
    | PLLetFun y fn D' => if string_dec x y then Some (inl fn) else getDef D' x (* y ≠ x *)
    end.

  (* Attackers are third-party libraries linked with the compiled program, e.g., stdlibs, runtime supports, ... *)
  Inductive Ctx__LS : Set := (* C *)
  | CLHole (* [] *)
  | CLLet : (Id__LS * Type__LS) -> Val__LS -> Ctx__LS -> Ctx__LS (* let x : τ = e1 in C *)
  | CLLetFun : Id__LS -> Fun__LS -> Ctx__LS -> Ctx__LS. (* let x = λ (y : τ). (e1 : τ) in C *)

  (** This is the heap (modelled as a stack :) *)
  Definition Frame__LS := BufAddr__LS -> BufOff__LS -> option Val__LS.
  Definition Heap__LS := list Frame__LS.

  (* Verifies that the top frame of H includes the specified buffer defined at offset n  *)
  Fixpoint belongsBuf (H : Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) :=
    match H with
    | h::hs => match h b n with None => False | _ => True end
    | _ => False
    end.

  Fixpoint structSize (rec : Val__LS) : nat :=
    match rec with
    | LVRec fl => List.length fl
    | _ => 0
    end.

  Program Fixpoint findField (rec : Val__LS) (f : FId__LS) {measure (structSize rec)} : option Val__LS :=
    match rec with
    | LVRec ((f', v)::tl) => if string_dec f f' then Some v else findField (LVRec tl) f
    | _ => None
    end.

  Fixpoint getStruct (rec : Val__LS) (fl : list FId__LS) : option Val__LS :=
    match fl with
    | f::[] => findField rec f
    | f::fl => match findField rec f with
             | None => None
             | Some v => getStruct v fl
             end
    | [] => None
    end.

  (* Verifies that the top frame of H includes the specified buffer defined at the offset n.
     If that's the case then it checks whether the content of b+n is (nested) structure s.t. the path fl is defined *)
  Fixpoint belongsStruct (H : Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) (fl : list FId__LS) :=
    match H with
    | h::hs => match h b n with
             | None => False
             | Some v => match getStruct v fl with None => False | _ => True end
             end
    | _ => False
    end.

  (* Heap access *)
  Fixpoint readBuf (H :  Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) : option Val__LS:=
    match H with
    | h::hs => h b n
    | _ => None
    end.

  Fixpoint readStruct (H : Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) (lf : list FId__LS) : option Val__LS:=
    match H with
    | h::hs => match h b n with None => None | Some v => getStruct v lf end
    | _ => None
    end.

  (* Heap writing of a buffer: if anything goes wrong leave it unchanged! *)
  Fixpoint writeBuf (H :  Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) (v : Val__LS) : Heap__LS :=
    match H with
    | h::hs => (fun b' n' => if andb (b == b') (n == n') then Some v else h b' n')::hs
    | _ => H
    end.

  Program Fixpoint setFieldAux acc rec f v {measure (structSize rec)} :=
    match rec with
    | LVRec ((f', v')::tl) => if string_dec f f'
                            then LVRec (acc ++ [(f', v)] ++ tl)
                            else setFieldAux (acc ++ [(f', v')]) (LVRec tl) f v
    | _ => rec
    end.

  Fixpoint setField (rec : Val__LS) (f : FId__LS) (v : Val__LS) : Val__LS := setFieldAux [] rec f v.

  Fixpoint setStruct (rec : Val__LS) (fl : list FId__LS) (v : Val__LS) : Val__LS :=
    match fl with
    | f::[] => setFieldAux [] rec f v
    | f::fl' => match findField rec f with
             | None => rec
             | Some v => setStruct rec fl' v
             end
    | [] => rec
    end.


  (* Heap writing of a struct: if anything goes wrong leave it unchanged! *)
  Fixpoint writeStruct (H :  Heap__LS) (b : BufAddr__LS) (n : BufOff__LS) (fl : list FId__LS) (v : Val__LS) : Heap__LS :=
    match H with
    | h::hs => (fun b' n' => if andb (b == b') (n == n') then Some v else h b' n')::hs
    | _ => H
    end.

  (* Programs are code - e - and function definitions - D - *)
  Definition Par__LS : Set := (Prog__LS * Exp__LS). (* S = (D, e) *)
  (* Whole programs also include an heap *)
  Definition Whole__LS : Set := (Heap__LS * Prog__LS * Exp__LS). (* W = (H, D, e) *)

  (*
    This function describes the linking, may be at load time (e.g., with DLLs or with AOT/JIT compilers) or in the final phases of compilation, in case of static linking.
   *)
  Fixpoint link__LS (C : Ctx__LS) (S : Par__LS) : Whole__LS :=
    let D := (fix decl_link__LS (C : Ctx__LS) (D : Prog__LS) : Prog__LS := match C with
                                                                | CLHole => D
                                                                | CLLet x e C' => PLLet x e (decl_link__LS C' D)
                                                                | CLLetFun f fn C' => PLLetFun f fn (decl_link__LS C' D)
                                                                end) C (fst S) in
    ([], D, snd S).

  Local Notation "C [ S ]" := (link__LS C S) (at level 70).

  (* This is what we are interested in observing (could be used to approx. non-interference props) *)
  Inductive SOb : Set :=
  | OEmp
  | OBrT | OBrF (* True and false branching, resp. *)
  | ORead : BufAddr__LS -> BufOff__LS -> list FId__LS -> SOb (* Read buffer or structure  *)
  | OWrite : BufAddr__LS -> BufOff__LS -> list FId__LS -> SOb. (* Write buffer or structure  *)

  Definition Obs : Set := list SOb.
  (**
     This is the semantics of λow* from ICFP paper.

     TODO: investigate the differences between Low* (as in the output of KreMLin last optimization step before C* ) and λow*. Can we deal with real programs here? How?

     TODO: unclear what the paper-and-pencil proof from ICFP'17 guarantees:
           - correctness for sure, but what about robust preservation?
           - ref. and dep. types are not in λow*, but guarantees should be preserved:
                  + if a robust safety is proved in the source then is the bisimulation proof to C* enough? i.e., is the bisimulation a congruence?

                  + from C* to Clights things are clearer since the proof is done via simulation, thus enough to preserve properties non-robustly.

     ** Overall: correctness proof, though not mechanized (error-prone) for a 2 yrs old version of the compiler. No robust preservation in the "complete" case. **
     *)
  Fixpoint substVar (e : Exp__LS) (x : Id__LS) (v : Val__LS) : Exp__LS := LVal LVUnit.
  Local Notation "e { x / v }" := (substVar e x v) (at level 100).

  (* Head reduction, i.e., P ⊢ (H, e) ⇾ (H', e') *)
  Inductive vstep__LS : Whole__LS -> Obs -> Whole__LS -> Prop :=
  | ReadBuf : forall H b n n' v D x τ e,
      (readBuf H b (n + n') = Some v) ->
      vstep__LS (H, D, LRBuf (x, τ) (LVal (LVMut b n []), LVal n') e) [ORead b (n + n') []] (H, D, substVar e x v)
  | ReadStruct : forall H b n fl v D x τ e,
      (readStruct H b n fl = Some v) ->
      vstep__LS (H, D, LRStruct (x, τ) (LVal (LVMut b n fl)) e) [ORead b n fl] (H, D, substVar e x v)
  | App : forall D f y τ e1 τ1 H x τ__x v e,
      (getDef D f = Some (inl ((y, τ), (e1, τ1)))) ->
      vstep__LS (H, D, LApp (x, τ__x) (f, LVal v) e) [OEmp] (H, D, LLet (x, τ__x) (substVar e1 y v) e)
  | WriteBuf : forall H b n n' D v e,
      belongsBuf H b (n + n') ->
      vstep__LS (H, D, LWBuf (LVal (LVMut b n []), LVal n', LVal v) e) [OWrite b (n + n') []] (writeBuf H b n v, D, e) 
  | WriteStruct : forall H b n fl D v e,
      belongsStruct H b n fl ->
      vstep__LS (H, D, LWStruct (LVal (LVMut b n fl), LVal v) e) [OWrite b n fl] (writeStruct H b n fl v, D, e) 
  .

  Inductive step__LS : Whole__LS -> Obs -> Whole__LS -> Prop :=
  | Step : forall H D W o H' W' E,
    vstep__LS (H, D, W) o (H', D, W') ->
    step__LS (link__EV H D E W) o (link__EV H D E W).

  Definition Lang := Framework.Build_language Whole__LS Exp__LS Ctx__LS link__LS step__LS.


  (*
      Inductive Exp__LS : Set := (* e *)
  | LRBuf : (Id__LS * Type__LS) -> (Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let x = readbuf e1 e2 in e *)
  | LWBuf : (Exp__LS * Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let _ = writebuf e1 e2 e3 in e *)  
  | LNBuf : Id__LS -> BufOff__LS -> (Exp__LS * Type__LS) -> Exp__LS -> Exp__LS (* let x = newbuf n (e1 : τ) in e *)
  | LSubbuf : Exp__LS -> Exp__LS -> Exp__LS (* subbuf e1 e2 *)
  | LRStruct : (Id__LS * Type__LS) -> Exp__LS -> Exp__LS -> Exp__LS (* Let x : τ = readstruct e1 in e *)
  | LWStruct : (Exp__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let _ = writestruct e1 e2 in e *)  
  | LNStruct : Id__LS -> (Exp__LS * Type__LS) -> Exp__LS -> Exp__LS (* let x = newstruct (e1 : τ) in e *)
  | LMProj : Exp__LS -> FId__LS -> Exp__LS (* e ▷ f *)
  | LWith : Exp__LS -> Exp__LS (* withframe e *)
  | LPop : Exp__LS -> Exp__LS (* pop e *)
  | LIfThenElse : Exp__LS -> Exp__LS -> Exp__LS (* if e1 then e2 else e3 *)
  | LApp : (Id__LS * Type__LS) -> (Id__LS * Exp__LS) -> Exp__LS -> Exp__LS (* let x : τ = fn e1 in e *)
  | LLet : (Id__LS * Type__LS) -> Exp__LS -> Exp__LS -> Exp__LS (* let x : τ = e1 in e *)
  | LLetFun : Id__LS -> (Id__LS * Type__LS) -> (Exp__LS * Type__LS) -> Exp__LS -> Exp__LS (* let x = λ (y : τ). (e1 : τ) in e *)
  | LRec : list (FId__LS * Exp__LS) -> Exp__LS (* { f0 = e0, ..., fn = en } *)
  | LIProj : Exp__LS -> FId__LS -> Exp__LS (* e.f *)
  | LVal : Val__LS -> Exp__LS. (* v *)

  Inductive Val__LS := (* v *)
  | LUnit 
  | LVar : Id__LS -> Val__LS
  | LInt : int -> Val__LS
  | LVRec : list (FId__LS * Val__LS) -> Val__LS
  | LMut : BufAddr__LS -> BufOff__LS -> list FId__LS -> Val__LS.
   *)
End Source.
