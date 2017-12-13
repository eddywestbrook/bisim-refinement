Require Export BisimRefinement.TraceMonad.
Require Export BisimRefinement.BisimPerm.

Require Export Coq.Arith.PeanoNat.
Require Export Coq.Lists.List.


(***
 *** Machine Values
 ***)

(* Values in our simple machine are just nats *)
Inductive SMValue := | mkSMValue (n:nat).

(* The "undefined" value *)
(* Definition undefValue := mkSMValue 0. *)

(* Values are related by the built-in Coq intensional equality *)
Instance LR_SMValue : LR SMValue := LR_eq.

(* Test equality of values *)
Definition val_eqb (v1 v2 : SMValue) : bool :=
  match v1, v2 with
    mkSMValue n1, mkSMValue n2 => Nat.eqb n1 n2
  end.

(* Test if a value is "true", represented here as not equal to 0 *)
Definition val_true (v: SMValue) : bool :=
  match v with
    mkSMValue n => negb (Nat.eqb n 0)
  end.

(* A tuple of 0 or more values *)
Definition SMValues n := NTuple SMValue n.

Instance LR_SMValues n : LR (SMValues n) := Build_LR _ _ _.


(***
 *** Register Sets
 ***)

(* A set of SSA register values *)
Definition SMRegs := list SMValue.

Instance LR_SMRegs : LR SMRegs := LR_eq.

(* Read a register value *)
Definition readReg (regs:SMRegs) n : option SMValue := nth_error regs n.

(* Push a new register value *)
Definition pushReg (regs:SMRegs) val : SMRegs := val :: regs.

(* Push a list of new register values *)
Fixpoint pushRegs (regs:SMRegs) n : SMValues n -> SMRegs :=
  match n return SMValues n -> SMRegs with
  | 0 => fun _ => regs
  | S n' => fun vals => pushRegs (pushReg regs (fst vals)) n' (snd vals)
  end.


(***
 *** Data Memories
 ***)

(* A data memory = a map from "pointers" (represented by nats) to values (which
are also nats) *)
Inductive DataMem := mkDataMem (vmap: nat -> SMValue).

(* Data memories are related by extensional functional equivalence *)
Instance LR_DataMem : LR DataMem :=
  { lr_leq := fun dmem1 dmem2 =>
                match dmem1, dmem2 with
                | mkDataMem vmap1, mkDataMem vmap2 => vmap1 <lr= vmap2
                end;
  }.
Proof.
  constructor.
  - intros [ vmap ]; reflexivity.
  - intros [ vmap1 ] [ vmap2 ] [ vmap3 ] R12 R23; etransitivity; eassumption.
Defined.

(* Read a pointer value *)
Definition readPtr (mem:DataMem) (ptr:SMValue) : SMValue :=
  match mem, ptr with
  | mkDataMem vmap, mkSMValue n => vmap n
  end.

Instance Proper_readPtr : Proper (lr_leq ==> lr_leq ==> lr_leq) readPtr.
Proof.
  intros [ vmap1 ] [ vmap2 ] R_vmap [ n1 ] [ n2 ] Rn. simpl in Rn.
  rewrite Rn. apply R_vmap.
Qed.

Instance Proper_readPtr_equiv : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) readPtr.
Proof.
  intros mem1 mem2 [ Rmem Rmem' ] ptr1 ptr2 [ Rptr Rptr' ].
  split; apply Proper_readPtr; assumption.
Qed.

(* Write a pointer value *)
Definition writePtr (mem:DataMem) ptr val : DataMem :=
  match mem, ptr with
  | mkDataMem vmap, mkSMValue n =>
    mkDataMem (fun n' => if Nat.eqb n n' then val else vmap n')
  end.

Instance Proper_writePtr :
  Proper (lr_leq ==> lr_leq ==> lr_leq ==> lr_leq) writePtr.
Proof.
  intros [ vmap1 ] [ vmap2 ] R_vmap [ ptr1 ] [ ptr2 ] Rptr
         [ v1 ] [ v2 ] Rv. simpl in Rptr, Rv. rewrite Rptr. rewrite Rv.
  intro n. destruct (Nat.eqb ptr2 n); try reflexivity; apply R_vmap.
Qed.

Instance Proper_writePtr_equiv :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv ==> lr_equiv) writePtr.
Proof.
  intros mem1 mem2 [ Rmem Rmem' ] ptr1 ptr2 [ Rptr Rptr' ] v1 v2 [ Rv Rv' ].
  split; apply Proper_writePtr; assumption.
Qed.

(* readPtr and writePtr form a lens *)
Program Definition ptr_dmem_lens (ptr: SMValue) : Lens DataMem SMValue :=
  {| getL mem := readPtr mem ptr;
     putL val mem := writePtr mem ptr val; |}.
Next Obligation.
  intros mem1 mem2 eq_mem. rewrite eq_mem. reflexivity.
Defined.
Next Obligation.
  intros v1 v2 eq_v mem1 mem2 eq_mem. rewrite eq_mem. rewrite eq_v. reflexivity.
Defined.
Next Obligation.
  destruct a as [ vmap ]. destruct ptr as [ ptr ].
  split; intro n; case_eq (Nat.eqb ptr n); intro; try reflexivity.
  - rewrite Nat.eqb_eq in H. rewrite H. reflexivity.
  - rewrite Nat.eqb_eq in H. rewrite H. reflexivity.
Defined.
Next Obligation.
  destruct a as [ vmap ]. destruct ptr as [ ptr ]. destruct b as [ v ].
  simpl. rewrite (proj2 (Nat.eqb_eq _ _) eq_refl). reflexivity.
Defined.
Next Obligation.
  destruct a as [ vmap ]. destruct ptr as [ ptr ].
  destruct b1 as [ v1 ]. destruct b2 as [ v2 ].
  split; intro n; case_eq (Nat.eqb ptr n); intro; reflexivity.
Defined.


(***
 *** Machine Expressions
 ***)

(* A "machine expression" is any value you can build from the registers,
possibly with an error *)
Definition SMExpr := SMRegs -> option SMValue.

Instance LR_SMExpr : LR SMExpr := Build_LR _ _ _.

(* The expression that returns an undefined value *)
(* Definition undefSMExpr : SMExpr := fun _ => undefValue. *)

(* A tuple of expressions with a fixed size *)
Definition SMExprs (n:nat) := NTuple SMExpr n.

Instance LR_SMExprs n : LR (SMExprs n) := Build_LR _ _ _.


(***
 *** Machine Instructions
 ***)

Inductive SMInstr : nat -> Type :=

(* Assign values to the next registers *)
| SMAssign n (exprs: SMExprs n) : SMInstr n

(* Read a value from memory into the next register *)
| SMRead (ptr: SMExpr) : SMInstr 1

(* Write a value to memory *)
| SMWrite (ptr val: SMExpr) : SMInstr 0

(* Call a function pointer; calls always have 1 return value *)
| SMCall (fptr: SMExpr) : SMInstr 1

(* If-then-else, where the SSA phi node with N variables is represented as
having the two bodies return N values *)
| SMIf n (expr: SMExpr) (body1 body2: SMBlock n) : SMInstr n

(* While loop, where the SSA phi node with N variables is represented as having
the body return N values and having N default return values for the case that no
iterations happen *)
| SMWhile n (expr: SMExpr) (init:SMExprs n) (body:SMBlock n) : SMInstr n

with
SMBlock : nat -> Type :=

(* Return n values as the result of the block *)
| SMReturn n (exprs: SMExprs n) : SMBlock n

(* Run an instruction with n return values, push them into the next registers,
and then execute the remainder of the block in that extended context *)
| SMLet n (inst: SMInstr n) m (rest: SMBlock m) : SMBlock m
.


(* FIXME: using Coq intensional equality here adds a dependency on functional
extensionality to express equality of SMExprs, which is not really
necessary. Instead, these relations should be defined inductively on
instructions on blocks, using LR_SMExprs where needed. *)
Instance LR_SMInstr n : LR (SMInstr n) := LR_eq.
Instance LR_SMBlock n : LR (SMBlock n) := LR_eq.


(***
 *** Instruction Memories
 ***)

(* An instruction memory = a partial map from "pointers" (represented by nats)
to function bodies with 1 return value *)
Inductive InstMem : Type := mkInstMem (imap:nat -> option (SMBlock 1)).

(* Instruction memories are related by the built-in Coq intensional equality *)
Instance LR_InstMem : LR InstMem := LR_eq.

(* Read a function pointer to get a function body, defaulting to "return undef"
if the function pointer does not have a binding *)
Definition readFunPtr (mem:InstMem) (fptr:SMValue) : option (SMBlock 1) :=
  match mem, fptr with
  | mkInstMem imap, mkSMValue n => imap n
  end.


(***
 *** Machine States
 ***)

(* A machine state = registers and two types of memory *)
Definition SMState : Type := (SMRegs * (DataMem * InstMem)).

Instance LR_SMState : LR SMState := Build_LR _ _ _.

(* Lenses for the top-level components of SMState *)
Definition regs_lens : Lens SMState SMRegs := fst_lens _ _.
Definition dmem_lens : Lens SMState DataMem :=
  compose_lens (snd_lens _ _) (fst_lens _ _).
Definition imem_lens : Lens SMState InstMem :=
  compose_lens (snd_lens _ _) (snd_lens _ _).

(* The lens for a pointer into the DataMem of an SMState *)
Definition ptr_lens (ptr: SMValue) : Lens SMState SMValue :=
  compose_lens dmem_lens (ptr_dmem_lens ptr).


(***
 *** Machine Semantics
 ***)

(* The monad for executing simple machines *)
Definition SMMonad A `{LR A} := TraceM SMState A.

(* Evaluate an expression in a monad *)
Definition evalExpr (expr: SMExpr) : SMMonad SMValue :=
  bindM getM (fun smst =>
                match expr (getL regs_lens smst) with
                | Some v => returnM v
                | None => errorM
                end).

(* Evaluate a tuple of expressions in a monad *)
Fixpoint evalExprs {n} : SMExprs n -> SMMonad (SMValues n) :=
  match n return SMExprs n -> SMMonad (SMValues n) with
  | 0 => fun _ => returnM tt
  | S n' =>
    fun exprs =>
      bindM (evalExpr (fst exprs))
            (fun v =>
               bindM (evalExprs (snd exprs))
                     (fun vs => returnM (v, vs)))
  end.

(* Evaluate a machine instruction in a monad, assuming a recursive helper
function to "tie the knot" when evaluating function pointers *)
Fixpoint evalInstr' (recEval: SMBlock 1 -> SMMonad (SMValues 1))
         {n} (inst: SMInstr n) : SMMonad (SMValues n) :=
  match inst with
  | SMAssign n exprs =>
    evalExprs exprs
  | SMRead ptr_expr =>
    bindM (evalExpr ptr_expr)
          (fun ptr =>
             bindM getM (fun smst =>
                           returnM (getL (ptr_lens ptr) smst, tt)))
  | SMWrite ptr_expr val_expr =>
    bindM (evalExpr ptr_expr)
          (fun ptr =>
             bindM (evalExpr val_expr)
                   (fun val =>
                      bindM getM
                            (fun smst =>
                               putM (putL (ptr_lens ptr) val smst))))
  | SMCall fptr_expr =>
    bindM (evalExpr fptr_expr)
          (fun fptr =>
             bindM getM
                   (fun smst =>
                      match readFunPtr (getL imem_lens smst) fptr with
                      | Some block => recEval block
                      | None => errorM
                      end))
  | SMIf n expr body1 body2 =>
    bindM (evalExpr expr)
          (fun v =>
             if val_true v then
               evalBlock' recEval body1
             else
               evalBlock' recEval body2)
  | SMWhile n expr init_exprs body =>
    bindM (evalExprs init_exprs)
          (fun init_vs =>
             fixM (fun f prev_vs =>
                     bindM (evalExpr expr)
                           (fun v =>
                              if val_true v then
                                bindM (evalBlock' recEval body)
                                      (fun new_vs =>
                                         f new_vs)
                              else
                                returnM prev_vs))
                  init_vs)
  end

with
evalBlock' (recEval: SMBlock 1 -> SMMonad (SMValues 1))
          {n} (block: SMBlock n) : SMMonad (SMValues n) :=
  match block with
  | SMReturn n exprs =>
    evalExprs exprs
  | SMLet n inst m rest =>
    bindM (evalInstr' recEval inst)
          (fun vs =>
             bindM getM
                   (fun smst =>
                      bindM (putM (modifyL regs_lens
                                           (fun regs => pushRegs regs _ vs)
                                           smst))
                            (fun _ => evalBlock' recEval rest)))
  end.

(* Tie the knot for evalBlock on a function body (with 1 return value) *)
Definition evalFunBody : SMBlock 1 -> SMMonad (SMValues 1) :=
  fixM (fun recEval body => evalBlock' recEval body).

(* Tie the knot for evalInstr *)
Definition evalInstr {n} (inst: SMInstr n) : SMMonad (SMValues n) :=
  evalInstr' evalFunBody inst.

(* Tie the knot for evalBlock *)
Definition evalBlock {n} (block: SMBlock n) : SMMonad (SMValues n) :=
  evalBlock' evalFunBody block.


