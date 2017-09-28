Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.


(***
 *** Computation Trees
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
  - intros tree1; induction tree1; intros tree2 tree3;
      destruct tree2; destruct tree3; simpl; intros;
        try auto; try contradiction.
    + destruct H; destruct H0; rewrite H; rewrite H0; rewrite H1; rewrite H2.
      split; reflexivity.
    + destruct H0; destruct H1. rewrite H0; rewrite H1; split; [ reflexivity | ].
      intro. apply (H _ _ _ (H2 _) (H3 _)).
Qed.

(* A "computation tree" is a prefix-closed set of finite trees *)
Record CompTree St A : Type :=
  { ctIn : FinCompTree St A -> Prop;
    ctClosed : forall tree1 tree2,
        extendsFCT tree2 tree1 -> ctIn tree1 -> ctIn tree2 }.

Arguments ctIn {St A} _.
Arguments ctClosed {St A} _.

Definition extendsFT {St A} : relation (CompTree St A) :=
  fun tree1 tree2 =>
    forall fct, ctIn tree1 fct -> ctIn tree2 fct.

Instance PreOrder_extendsFT {St A} : PreOrder (@extendsFT St A).
Proof.
  constructor.
  - intros tree fct H; assumption.
  - intros tree1 tree2 tree3 R12 R23 fct fct_in.
    apply R23. apply R12. assumption.
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
