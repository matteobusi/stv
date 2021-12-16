Require List.
Require Streams.
Require String.
Require Bool.

Require Classical.
Require Classical_Prop.

Require ClassicUtils.

Require Common.

Require Trg.
Require Src.


Module Backtranslation.
  Import Trg.
  Import Src.
  Import Common.
  Import String.
  Import List.
  Import Nat.

  Open Scope string_scope.
  Open Scope nat_scope.

  Definition max_buf_size := 100.
  Definition memory_size := 1000.

  Definition bt__j (u : iu_name) (f : fun_name) (j : Trg.j_inst) := match j with
                                                                  | Trg.JHalt => Src.EHalt::nil
                                                                  | Trg.JBnz r lt lf => (Src.EIfThenElse (Src.ERead "reg" (Src.EVal r))
                                                                                                       (Src.ECall u (f++"#"++lt) (Src.EVal 0))
                                                                                                       (Src.ECall u (f++"#"++lf) (Src.EVal 0)))::nil
                                                                  | Trg.JJmp l => (Src.ECall u (f++"#"++l) (Src.EVal 0))::nil
                                                                  | Trg.JCall u' f' lr =>
                                                                    (Src.ECall u' f' (Src.EVal 0))::(Src.ECall u f (Src.EVal 0))::nil
                                                                  | Trg.JRet => (Src.EAssign "arg" (Src.EVal 0) (Src.ERead "reg" (Src.EVal 0)))::nil
                                                                  end.

  Definition bt__c (u : iu_name) (i : Trg.c_inst) := match i with
                                                   | Trg.CNop => Src.EVal 42
                                                   | Trg.
                                                   end.

  Definition bt__d (u : iu_name) (dl : list Trg.def) : list Src.decl := nil.

  Fixpoint _bt__C (C__T : Trg.ctx) : Src.ctx :=
    match C__T with
    | Trg.CModule u i dl C'__T => Src.CCompartment u i (fun _ => Some max_buf_size) (bt__d u dl) (_bt__C C'__T) 
    | Trg.CHole => Src.CHole
    end.

    (* This includes the mem compartment is a "global" buffer: it has an internal buffer which is called mem which is accessible via three functions:
   - read l, returns the content of mem at location l
   - write_pre l, prepares to write the location l
   - write v, writes v in the location l where l is the last value provided via write_prepares
   *)
  Definition bt__C (C__T : Trg.ctx): Src.ctx :=
    Src.CCompartment "mem" "IMem" (fun _ => Some memory_size)
                     (Src.DFun "read" Src.EHalt::
                       Src.DFun "write_pre" Src.EHalt::
                       Src.DFun "write" Src.EHalt::nil)
                     (_bt__C C__T).

End Backtranslation.
