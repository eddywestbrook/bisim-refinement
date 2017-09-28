Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.


(***
 *** Logical Relations
 ***)

Class LR A : Type :=
  { lr_leq : relation A; lr_PreOrder :> PreOrder lr_leq }.

Instance LR_Reflexive A `{LR A} : Reflexive lr_leq.
Proof. typeclasses eauto. Qed.

Instance LR_Transitive A `{LR A} : Transitive lr_leq.
Proof. typeclasses eauto. Qed.

(* The equivalence relation for a logical relation *)
Definition lr_equiv {A} `{LR A} : relation A :=
  fun x y => lr_leq x y /\ lr_leq y x.

Instance lr_equiv_Equivalence A `{LR A} : Equivalence lr_equiv.
Proof.
  constructor; intro; intros.
  { split; reflexivity. }
  { destruct H0; split; assumption. }
  { destruct H0; destruct H1; split; transitivity y; assumption. }
Qed.

Notation "x <lr= y" :=
  (lr_leq x y) (no associativity, at level 70).
Notation "x =lr= y" :=
  (lr_equiv x y) (no associativity, at level 70).

(* FIXME: figure out what versions of this we need for rewriting! *)
Instance Proper_lr_leq_lr_leq A `{LR A}
  : Proper (lr_leq --> lr_leq ==> Basics.impl) (@lr_leq A _).
Proof.
  intros a1 a2 Ra b1 b2 Rb Rab.
  transitivity a1; [ assumption | ]. transitivity b1; assumption.
Qed.

Instance Subrelation_lr_equiv_lr_leq A `{LR A} :
  subrelation (@lr_equiv A _) lr_leq.
Proof.
  intros a1 a2 Ra; destruct Ra; assumption.
Qed.

Instance Proper_lr_equiv_lr_leq A `{LR A} :
  Proper (lr_equiv ==> lr_equiv ==> iff) (@lr_leq A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry; destruct Rx; destruct Ry; split; intro Rxy.
  transitivity x1; [ assumption | ]; transitivity y1; assumption.
  transitivity x2; [ assumption | ]; transitivity y2; assumption.
Qed.

Instance Proper_lr_equiv A `{LR A} :
  Proper (lr_equiv ==> lr_equiv ==> iff) (@lr_equiv A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry. rewrite Rx. rewrite Ry. reflexivity.
Qed.

Instance Proper_lr_equiv_partial A `{LR A} a :
  Proper (lr_equiv ==> Basics.flip Basics.impl) (@lr_equiv A _ a).
Proof.
  intros x1 x2 Rx. rewrite Rx. reflexivity.
Qed.


Instance LR_arrow {A B} `{LR B} : LR (A -> B) :=
  { lr_leq := fun f g => forall a, f a <lr= g a }.
Proof.
  constructor.
  - intros f a. reflexivity.
  - intros f g h Rfg Rgh a. transitivity (g a); [ apply Rfg | apply Rgh ].
Defined.

Instance LR_Prop : LR Prop :=
  { lr_leq := Basics.impl }.
Proof.
  constructor.
  - intros P H; assumption.
  - intros P1 P2 P3 impl12 impl23 pf; apply impl23; apply impl12; assumption.
Defined.


(***
 *** Finite Computation Trees
 ***)

Inductive FinCompTree St A : Type :=
| TreeStuck
| TreeLeaf (s:St) (a:A)
| TreeNode (s:St) (step: St -> FinCompTree St A)
.

Arguments TreeStuck {St A}.
Arguments TreeLeaf {St A} s a.
Arguments TreeNode {St A} s step.

Fixpoint extendsFCT {St A} (tree1 tree2 : FinCompTree St A) : Prop :=
  match (tree1, tree2) with
  | (TreeStuck, _) => True
  | (TreeLeaf s1 a1, TreeLeaf s2 a2) => s1 = s2 /\ a1 = a2
  | (TreeNode s1 step1, TreeNode s2 step2) =>
    s1 = s2 /\ forall s, extendsFCT (step1 s) (step2 s)
  | _ => False
  end.

Instance PreOrder_extendsFCT {St A} : PreOrder (@extendsFCT St A).
Proof.
  constructor.
  - intros tree; induction tree; simpl; auto.
  - intros tree1; induction tree1 as [ | | s a IH ];
      intros tree2 tree3;
      destruct tree2; destruct tree3; simpl; intros R12 R23;
        try auto; try contradiction.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23 | rewrite Ra12; rewrite Ra23 ];
        reflexivity.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23; reflexivity | ].
      intro. apply (IH _ _ _ (Ra12 _) (Ra23 _)).
Qed.

Instance LR_FinCompTree {St A} : LR (FinCompTree St A) :=
  { lr_leq := extendsFCT; lr_PreOrder := _ }.


(***
 *** Computation Trees
 ***)

(* A "computation tree" is a prefix-closed set of finite trees *)
Record CompTree St A : Type :=
  { ctIn : FinCompTree St A -> Prop;
    ctClosed : forall tree1 tree2,
        extendsFCT tree2 tree1 -> ctIn tree1 -> ctIn tree2 }.

Arguments ctIn {St A} _.
Arguments ctClosed {St A} _.

Instance LR_CompTree St A : LR (CompTree St A) :=
  { lr_leq := fun tree1 tree2 => lr_leq (ctIn tree1) (ctIn tree2) }.
Proof.
  constructor.
  - intro. reflexivity.
  - intros tree1 tree2 tree3; transitivity (ctIn tree2); assumption.
Qed.


Program Definition downCloseTree {St A} tree : CompTree St A :=
  {|
    ctIn := fun tree' => lr_leq tree' tree;
  |}.
Next Obligation.
  etransitivity; eassumption.
Defined.

Instance Proper_downCloseTree St A :
  Proper (lr_leq ==> lr_leq) (@downCloseTree St A).
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** Stateful Monads
 ***)

Class MonadStateOps M St : Type :=
  {
    returnM : forall {A}, A -> M A;
    bindM : forall {A B}, M A -> (A -> M B) -> M B;
    getM : M St;
    putM : St -> M unit;
  }.

Class MonadState M St `{MonadStateOps M St} : Type :=
  {
    Monad_LR {A} :> LR (M A);

    Proper_bindM {A B} :
      Proper (lr_leq ==> lr_leq ==> lr_leq) (bindM (A:=A) (B:=B));

    monad_return_bind {A B} a (f : A -> M B) :
      bindM (returnM a) f =lr= f a;
    monad_bind_return {A} (m : M A) :
      bindM m returnM =lr= m;
    monad_assoc {A B C} m (f: A -> M B) (g: B -> M C) :
      bindM (bindM m f) g =lr= bindM m (fun x => bindM (f x) g);

    (* FIXME HERE: write the monad laws! *)
  }.


(***
 *** The Finite Trace Monad
 ***)

Definition FinTraceMonad St A := St -> FinCompTree St A.

Fixpoint bindFinTree {St A B} (fct: FinCompTree St A)
         (f : A -> FinTraceMonad St B) : FinCompTree St B :=
  match fct with
  | TreeStuck => TreeStuck
  | TreeLeaf s a => f a s
  | TreeNode s step =>
    TreeNode s (fun s' => bindFinTree (step s') f)
  end.

Instance Proper_bindFinTree St A B :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (@bindFinTree St A B).
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadStateOps_FinTraceMonad St : MonadStateOps (FinTraceMonad St) St :=
  {|
    returnM := fun A a s => TreeLeaf s a;
    bindM := fun A B m f s => bindFinTree (m s) f;
    getM := fun s => TreeLeaf s s;
    putM := fun s _ => TreeLeaf s tt
  |}.

Instance MonadState_FinTraceMonad St : MonadState (FinTraceMonad St) St.
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The Trace Monad
 ***)

Definition TraceMonad St A := St -> CompTree St A.

Definition downCloseM {St A} (m: FinTraceMonad St A) : TraceMonad St A :=
  fun s => downCloseTree (m s).


FIXME HERE NOW: write bindTree!

Program Definition bindTree {St A B} (tree: CompTree St A)
        (f: A -> TraceMonad St B) : CompTree St B :=
  {| ctIn := fun ftreeB =>
               exists 

Instance MonadStateOps_TraceMonad St : MonadStateOps (TraceMonad St) St :=
  {|
    returnM := fun A a => downCloseM (returnM a);
    bindM :=
      fun A B m f =>
        


Definition approxTM {St A} `{LR A}
           (m: TraceMonad St A) (ftm: FinTraceMonad St A) : Prop :=
  forall s, ctIn (m s) (ftm s).

Definition stepsTo1 {St A} `{LR A} : relation (St * TraceMonad St A) :=
  fun stm1 stm2 =>
    forall ftm,
      approxTM (snd stm2) ftm
      <-> ctIn ((snd stm1) (fst stm1)) (TreeNode (fst stm2) ftm).
