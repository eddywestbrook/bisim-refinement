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

Fixpoint extendsFCT {St A} `{LR A} (tree1 tree2 : FinCompTree St A) : Prop :=
  match (tree1, tree2) with
  | (TreeStuck, _) => True
  | (TreeLeaf s1 a1, TreeLeaf s2 a2) => s1 = s2 /\ lr_leq a1 a2
  | (TreeNode s1 step1, TreeNode s2 step2) =>
    s1 = s2 /\ forall s, extendsFCT (step1 s) (step2 s)
  | _ => False
  end.

Instance PreOrder_extendsFCT {St A} `{LR A} : PreOrder (@extendsFCT St A _).
Proof.
  constructor.
  - intros tree; induction tree; simpl; auto. split; reflexivity.
  - intros tree1; induction tree1; intros tree2 tree3;
      destruct tree2; destruct tree3; simpl; intros;
        try auto; try contradiction.
    + destruct H0; destruct H1.
      split; [ rewrite H0; rewrite H1 | rewrite H2; rewrite H3 ]; reflexivity.
    + destruct H1; destruct H2.
      split; [ rewrite H1; rewrite H2; reflexivity | ].
      intro. apply (H0 _ _ _ (H3 _) (H4 _)).
Qed.

Instance LR_FinCompTree {St A} `{LR A} : LR (FinCompTree St A) :=
  { lr_leq := extendsFCT; lr_PreOrder := _ }.


(***
 *** Computation Trees
 ***)

(* A "computation tree" is a prefix-closed set of finite trees *)
Record CompTree St A `{LR A} : Type :=
  { ctIn : FinCompTree St A -> Prop;
    ctClosed : forall tree1 tree2,
        extendsFCT tree2 tree1 -> ctIn tree1 -> ctIn tree2 }.

Arguments ctIn {St A _} _.
Arguments ctClosed {St A _} _.

Instance LR_CompTree St A `{LR A} : LR (CompTree St A) :=
  { lr_leq := fun tree1 tree2 => lr_leq (ctIn tree1) (ctIn tree2) }.
Proof.
  constructor.
  - intro. reflexivity.
  - intros tree1 tree2 tree3; transitivity (ctIn tree2); assumption.
Qed.


(***
 *** The Trace Monad
 ***)

Definition TraceMonad St A := St -> CompTree St A.

Definition FinTraceMonad St A := St -> FinCompTree St A.

Definition extendsFTM {St A} : relation (FinTraceMonad St A) :=
  fun m1 m2 => forall s, extendsFCT (m1 s) (m2 s).

Definition approxTM {St A} (m: TraceMonad St A) (ftm: FinTraceMonad St A) : Prop :=
  forall s, ctIn (m s) (ftm s).

Definition stepsTo1 {St A} : relation (St * TraceMonad St A) :=
  fun stm1 stm2 =>
    forall ftm,
      approxTM (snd stm2) ftm
      <-> ctIn ((snd stm1) (fst stm1)) (TreeNode (fst stm2) ftm).
