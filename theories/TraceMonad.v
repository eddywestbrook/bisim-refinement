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
  { lr_leq P1 P2 := P1 -> P2 }.
Proof.
  constructor.
  - intros P H; assumption.
  - intros P1 P2 P3 impl12 impl23 pf; apply impl23; apply impl12; assumption.
Defined.


(***
 *** Downward Closed Sets
 ***)

Record DownSet A `{LR A} : Type :=
  { inDownSet : A -> Prop;
    downSetClosed :
      forall a1 a2, lr_leq a2 a1 -> inDownSet a1 -> inDownSet a2 }.

Arguments inDownSet {A _} _ _.
Arguments downSetClosed {A _} _.

Instance LR_DownSet A `{LR A} : LR (DownSet A) :=
  {| lr_leq ds1 ds2 := lr_leq (inDownSet ds1) (inDownSet ds2) |}.
Proof.
  constructor.
  - intro. reflexivity.
  - intros ds1 ds2 ds3; transitivity (inDownSet ds2); assumption.
Defined.

Program Definition downClose {A} `{LR A} (a:A) : DownSet A :=
  {| inDownSet a' := lr_leq a' a |}.
Next Obligation.
  etransitivity; eassumption.
Defined.

Instance Proper_downClose A `{LR A} :
  Proper (lr_leq ==> lr_leq) (downClose (A:=A)).
Proof.
  intros a1 a2 R12 a'; simpl; intro in_a'. etransitivity; eassumption.
Qed.

Program Definition bindDownSet {A B} `{LR A} `{LR B}
           (dsA: DownSet A) (f: A -> DownSet B) : DownSet B :=
  {| inDownSet := fun b => exists a, inDownSet dsA a /\ inDownSet (f a) b;
     downSetClosed := _ |}.
Next Obligation.
  exists H2; split; try assumption.
  apply (downSetClosed _ _ _ H1 H4).
Defined.

Instance Proper_bindDownSet A B `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (bindDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds f1 f2 Rf b; simpl; intro in_b.
  destruct in_b as [ a [in_ds1 in_f1]].
  exists a; split.
  - apply Rds; assumption.
  - apply Rf; assumption.
Qed.

Definition mapDownSet {A B} `{LR A} `{LR B} (f:A -> B) dsA : DownSet B :=
  bindDownSet dsA (fun a => downClose (f a)).

Definition lambdaDownSet {A B} `{LR A} `{LR B}
           (f: A -> DownSet B) : DownSet (A -> DownSet B) := downClose f.

Lemma Proper_lambdaDownSet {A B} `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq) (lambdaDownSet (A:=A) (B:=B)).
Proof.
  intros f1 f2 Rf. apply Proper_downClose. assumption.
Qed.

Lemma Proper_lambdaDownSet_equiv {A B} `{LR A} `{LR B} :
  Proper (lr_equiv ==> lr_equiv) (lambdaDownSet (A:=A) (B:=B)).
Proof.
  intros f1 f2 Rf. destruct Rf. split; apply Proper_downClose; assumption.
Qed.


Definition applyDownSet {A B} `{LR A} `{LR B}
           (dsF: DownSet (A -> DownSet B)) (a:A) : DownSet B :=
  bindDownSet dsF (fun f => f a).

Lemma Proper_applyDownSet A B `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq) (applyDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds a. apply Proper_bindDownSet; [ assumption | ].
  intro. reflexivity.
Qed.

Lemma Proper_applyDownSet_equiv A B `{LR A} `{LR B} :
  Proper (lr_equiv ==> lr_equiv) (applyDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds. destruct Rds.
  split; intro; apply Proper_applyDownSet; assumption.
Qed.


Lemma downSetBeta {A B} `{LR A} `{LR B} (f: A -> DownSet B) :
  applyDownSet (lambdaDownSet f) =lr= f.
Proof.
  split; simpl; intros.
  - destruct H1 as [g [Rgf in_ga]]. apply Rgf; assumption.
  - exists f; split; intros; assumption.
Qed.

(* NOTE: the reverse direction does not hold, because, e.g., dsF could be the
union of (downClose f) and (downClose g) where f and g have distinct sets as
their outputs for a, but (lambdaDownSet (applyDownSet dsF)) would have the union
of these sets as the output for a. *)
Lemma downSetEta {A B} `{LR A} `{LR B} (dsF : DownSet (A -> DownSet B)) :
  dsF <lr= lambdaDownSet (applyDownSet dsF).
Proof.
  simpl; intros. exists a. split; assumption.
Qed.


Program Definition fixDownSet {A} `{LR A} (f: DownSet A -> DownSet A) : DownSet A :=
  {| inDownSet a :=
       forall ds, f ds <lr= ds -> inDownSet ds a
  |}.
Next Obligation.
  apply (downSetClosed _ _ _ H0). apply H1. apply H2.
Defined.

Lemma fixDownSetUnfold {A} `{LR A} (f: DownSet A -> DownSet A)
      (prp: Proper (lr_leq ==> lr_leq) f) :
  (fixDownSet (A:=A) f) =lr= f (fixDownSet f).
Proof.
  assert (f (fixDownSet f) <lr= fixDownSet f).
  - intros a in_a ds ds_f_closed.
    assert (f (fixDownSet f) <lr= ds).
    + etransitivity; try eassumption. apply prp.
      intros a' in_a'. apply in_a'. assumption.
    + apply H0; assumption.
  - split; [ | apply H0 ].
    simpl; intros; apply (H1 _ (prp _ _ H0)).
Qed.

(* FIXME: come up with a better name for this! *)
Definition fixDownSetFun {A B} `{LR A} `{LR B}
           (f: (A -> DownSet B) -> (A -> DownSet B))
  : A -> DownSet B :=
  applyDownSet (fixDownSet (fun ds => lambdaDownSet (f (applyDownSet ds)))).

Lemma fixDownSetFunUnfold {A B} `{LR A} `{LR B}
      (f: (A -> DownSet B) -> (A -> DownSet B))
      (prp: Proper (lr_leq ==> lr_leq) f) :
  fixDownSetFun f =lr= f (fixDownSetFun f).
Proof.
  unfold fixDownSetFun.
  etransitivity.
  - apply Proper_applyDownSet_equiv. apply fixDownSetUnfold.
    intros ds1 ds2 Rds. apply Proper_lambdaDownSet. apply prp.
    apply Proper_applyDownSet. assumption.
  - rewrite downSetBeta. reflexivity.
Qed.


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
 *** Transition Monads
 ***)

Class MonadTraceOps M St : Type :=
  {
    returnM : forall {A}, A -> M A;
    bindM : forall {A B}, M A -> (A -> M B) -> M B;
    getM : M St;
    putM : St -> M unit;
    yieldM : M unit;
  }.

Class MonadTrace M St `{MonadTraceOps M St} : Type :=
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

    (* FIXME HERE: write the state monad laws! *)
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

Instance MonadTraceOps_FinTraceMonad St : MonadTraceOps (FinTraceMonad St) St :=
  {|
    returnM A a := fun s => TreeLeaf s a;
    bindM A B m f := fun s => bindFinTree (m s) f;
    getM := fun s => TreeLeaf s s;
    putM s := fun _ => TreeLeaf s tt;
    yieldM := fun s => TreeNode s (fun s => TreeLeaf s tt)
  |}.

Instance MonadTrace_FinTraceMonad St : MonadTrace (FinTraceMonad St) St.
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The Trace Monad
 ***)

Definition CompTree St A := DownSet (FinCompTree St A).

Program Definition TreeNodeF {St A} (s:St)
           (step: St -> CompTree St A) : CompTree St A :=
  {| inDownSet fct :=
         exists step',
           fct <lr= TreeNode s step' /\
           forall s', inDownSet (step s) (step' s')
  |}.
Next Obligation.
  destruct a1; simpl in H1; try contradiction;
    destruct a2; simpl in H; try contradiction; simpl.
  - exists H0; split; [ apply I | assumption ].
  - exists H0; split; [ apply I | assumption ].
  - destruct H as [ eq10 R10 ]; destruct H1 as [ eq0_ R0_ ].
    exists H0; split; [ split | ]; intros.
    + etransitivity; eassumption.
    + etransitivity; [ apply R10 | apply R0_ ].
    + apply H2.
Defined.

Definition TraceMonad St A := St -> CompTree St A.

Fixpoint bindFinTreeTM {St A B} (fct: FinCompTree St A)
        (f: A -> TraceMonad St B) : CompTree St B :=
  match fct with
  | TreeStuck => downClose TreeStuck
  | TreeLeaf s a => f a s
  | TreeNode s step =>
    TreeNodeF s (fun s' => bindFinTreeTM (step s') f)
  end.

Instance MonadTraceOps_TraceMonad St : MonadTraceOps (TraceMonad St) St :=
  {|
    returnM A a s := downClose (returnM a s);
    bindM A B m f s :=
      bindDownSet (m s) (fun fct => bindFinTreeTM fct f);
    getM s := downClose (getM s);
    putM s s' := downClose (putM s s');
    yieldM s := downClose (yieldM s);
  |}.

Instance MonadTrace_TraceMonad St : MonadTrace (TraceMonad St) St.
Proof.
  admit.
Admitted.


(***
 *** Computation Traces in the Trace Monad
 ***)

Definition stepsTo1 {St A} `{LR A} : relation (St * TraceMonad St A) :=
  fun stm1 stm2 =>
    TreeNodeF (fst stm2) (snd stm2) <lr= (snd stm1) (fst stm1).

Definition stepsTo {St A} `{LR A} := clos_trans _ (stepsTo1 (St:=St) (A:=A)).

Definition evalsTo1 {St A} `{LR A} (stm : St * TraceMonad St A) (res : St * A) :=
  inDownSet ((snd stm) (fst stm)) (TreeLeaf (fst res) (snd res)).

Definition evalsTo {St A} `{LR A} (stm : St * TraceMonad St A) (res : St * A) :=
  exists2 stm', stepsTo stm stm' & evalsTo1 stm' res.
