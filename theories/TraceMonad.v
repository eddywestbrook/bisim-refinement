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


Instance LR_unit : LR unit := { lr_leq := fun _ _ => True }.
Proof.
  constructor; intro; intros; apply I.
Defined.

Instance LR_pair {A B} `{LR A} `{LR B} : LR (A*B) :=
  { lr_leq := fun p1 p2 => fst p1 <lr= fst p2 /\ snd p1 <lr= snd p2 }.
Proof.
  constructor.
  - intro p. split; reflexivity.
  - intros p1 p2 p3 [ R12_l R12_r ] [ R23_l R23_r ].
    split; etransitivity; eassumption.
Defined.

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


(* NOTE: we make this a Definition and *NOT* an Instance so that typeclass
resolution does not use it everywhere *)
Definition LR_eq {A} : LR A := {| lr_leq := eq |}.

Class ConstLR (F : Type -> Type) : Type :=
  { lr_leq_K : forall {A}, LR (F A) }.

Instance LR_ConstLR F `{ConstLR F} A : LR (F A) := lr_leq_K.
Typeclasses Transparent LR_ConstLR.

(*
Class LRFunctor (F : Type -> Type) : Type :=
  { lr_leq_F : forall {A} `{LR A}, LR (F A) }.

Instance LR_LRFunctor F `{LRFunctor F} A `{LR A} : LR (F A) := lr_leq_F.
Typeclasses Transparent LR_LRFunctor.
*)


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

Program Definition unionDownSet {A} `{LR A} (ds1 ds2: DownSet A) : DownSet A :=
  {| inDownSet := fun a => inDownSet ds1 a \/ inDownSet ds1 a;
     downSetClosed := _ |}.
Next Obligation.
  destruct H1; [ left | right ]; eapply downSetClosed; eassumption.
Defined.

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

(* We define the fixed-point of a set function transformer f as the intersection
of all f-closed functions g *)
Program Definition fixDownSet {A B} `{LR A} `{LR B}
        (f: (A -> DownSet B) -> (A -> DownSet B)) (a:A) : DownSet B :=
  {| inDownSet b :=
       forall g, f g <lr= g -> inDownSet (g a) b
  |}.
Next Obligation.
  apply (downSetClosed _ _ _ H1). apply H2. apply H3.
Defined.

(* We then prove this is a fixed-point using the Knaster-Tarski theorem *)
Lemma fixDownSetUnfold {A B} `{LR A} `{LR B}
      (f: (A -> DownSet B) -> A -> DownSet B)
      (prp: Proper (lr_leq ==> lr_leq) f) :
  (fixDownSet (A:=A) (B:=B) f) =lr= f (fixDownSet f).
Proof.
  assert (f (fixDownSet f) <lr= fixDownSet f).
  - intros a b in_b g g_f_closed.
    assert (f (fixDownSet f) <lr= g).
    + etransitivity; try eassumption. apply prp.
      intros a' b' in_b'. apply in_b'. assumption.
    + apply H1; assumption.
  - split; [ | apply H1 ].
    simpl; intros; apply (H2 _ (prp _ _ H1)).
Qed.

Instance Proper_fixDownSet {A B} `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq) (fixDownSet (A:=A) (B:=B)).
Proof.
  admit. (* FIXME HERE *)
Admitted.


(* We can convert a function from A to sets of B to a set of functions from A to
B, by taking the set of all functions that are in f pointwise *)
Program Definition lambdaDownSet {A B} `{LR B}
        (f: A -> DownSet B) : DownSet (A -> B) :=
  {| inDownSet := fun g => forall a, inDownSet (f a) (g a); |}.
Next Obligation.
  eapply downSetClosed; [ apply H0 | apply H1 ].
Defined.

Instance Proper_lambdaDownSet {A B} `{LR B} :
  Proper (lr_leq ==> lr_leq) (lambdaDownSet (A:=A) (B:=B)).
Proof.
  intros f1 f2 R12 g in_g a. apply R12. apply in_g.
Qed.

Definition applyDownSet {A B} `{LR B}
           (dsF: DownSet (A -> B)) (a:A) : DownSet B :=
  mapDownSet (fun f => f a) dsF.

(* NOTE: applyDownSet is not Proper in its A argument unless we somehow build
Proper functions from the functions in dsF... *)
Instance Proper_applyDownSet {A B} `{LR B} :
  Proper (lr_leq ==> eq ==> lr_leq) (applyDownSet (A:=A) (B:=B)).
Proof.
  intros ds1 ds2 Rds a1 a2 eq_a b in_b. destruct in_b as [ g [ in_g1 in_g2 ]].
  rewrite <- eq_a.
  exists g. split.
  - apply Rds; assumption.
  - assumption.
Qed.

(* NOTE: the reverse only holds when f a is non-empty for all a; i.e., when
   there is some function g such that inDownSet (f a) (g a) for all a *)
Lemma downSetBeta {A B} `{LR B} (f: A -> DownSet B) :
  applyDownSet (lambdaDownSet f) <lr= f.
Proof.
  simpl; intros a b in_b.
  destruct in_b as [ g [ in_ga Rbg ]].
  eapply downSetClosed; [ apply Rbg | apply in_ga ].
Qed.


(***
 *** Transition Monads
 ***)

Class MonadTraceOps M St `{ConstLR M} : Type :=
  {
    (* Monadic return and bind *)
    returnM : forall {A}, A -> M A;
    bindM : forall {A B}, M A -> (A -> M B) -> M B;

    (* State operations *)
    getM : M St;
    putM : St -> M unit;

    (* Threading operations *)
    yieldM : M unit;
  }.

Class MonadTrace M St `{MonadTraceOps M St} : Prop :=
  {
    Proper_bindM {A B} :
      Proper (lr_leq ==> lr_leq ==> lr_leq) (bindM (A:=A) (B:=B));

    monad_return_bind {A B} a (f : A -> M B) :
      bindM (returnM a) f =lr= f a;
    monad_bind_return {A} (m : M A) :
      bindM m returnM =lr= m;
    monad_assoc {A B C} m (f: A -> M B) (g: B -> M C) :
      bindM (bindM m f) g =lr= bindM m (fun x => bindM (f x) g);

    (* FIXME: write the state and threading monad laws! *)
  }.

Class MonadForkJoinOps M : Type :=
  {
    forkJoinM : forall {A B}, M A -> M B -> M (A*B)%type;
  }.

Class MonadForkJoin M `{ConstLR M} `{MonadForkJoinOps M} : Prop :=
  {
    Proper_forkJoinM {A B} :
      Proper (lr_leq ==> lr_leq ==> lr_leq) (forkJoinM (A:=A) (B:=B));
    (* FIXME: write forkJoin laws...? *)
  }.

Class MonadForkOps M : Type :=
  {
    forkM : M unit -> M unit;
  }.

Class MonadFork M `{ConstLR M} `{MonadForkOps M} : Prop :=
  {
    Proper_forkM : Proper (lr_leq ==> lr_leq) (forkM (M:=M));
    (* FIXME: write fork laws...? *)
  }.

Class MonadFixOps M : Type :=
  {
    fixM : forall {A B} `{LR A} `{LR B},
      ((A -> M B) -> (A -> M B)) -> A -> M B;
  }.

Class MonadFix M `{ConstLR M} `{MonadFixOps M} : Prop :=
  {
    Proper_fixM {A B} `{LR A} `{LR B} :>
      Proper (lr_leq ==> lr_leq) (fixM (A:=A) (B:=B));
    fixM_correct :
      forall {A B} `{LR A} `{LR B} (f: (A -> M B) -> (A -> M B)),
        Proper (lr_leq ==> lr_leq) f ->
        fixM f =lr= f (fixM f)
  }.


(***
 *** Finite Computation Trees
 ***)

Inductive FinCompTree St A : Type :=
| CompStuck
| CompDone (s:St) (a:A)
| CompStep (s:St) (step: St -> FinCompTree St A)
| CompChoice : FinCompTree St A -> FinCompTree St A -> FinCompTree St A
.

Arguments CompStuck {St A}.
Arguments CompDone {St A} s a.
Arguments CompStep {St A} s step.
Arguments CompChoice {St A} tree1 tree2.

Fixpoint extendsFCT {St A} (tree1 tree2 : FinCompTree St A) : Prop :=
  match (tree1, tree2) with
  | (CompStuck, _) => True
  | (CompDone s1 a1, CompDone s2 a2) => s1 = s2 /\ a1 = a2
  | (CompStep s1 step1, CompStep s2 step2) =>
    s1 = s2 /\ forall s, extendsFCT (step1 s) (step2 s)
  | (CompChoice t1 t1', CompChoice t2 t2') =>
    extendsFCT t1 t2 /\ extendsFCT t1' t2'
  | _ => False
  end.

Instance PreOrder_extendsFCT {St A} : PreOrder (@extendsFCT St A).
Proof.
  constructor.
  - intros tree; induction tree; simpl; auto.
  - intros tree1; induction tree1 as [ | | s a IH | ];
      intros tree2 tree3;
      destruct tree2; destruct tree3; simpl; intros R12 R23;
        try auto; try contradiction.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23 | rewrite Ra12; rewrite Ra23 ];
        reflexivity.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23; reflexivity | ].
      intro. apply (IH _ _ _ (Ra12 _) (Ra23 _)).
    + destruct R12 as [ R12_1 R12_2 ]; destruct R23 as [ R23_1 R23_2 ].
      split; [ eapply IHtree1_1 | eapply IHtree1_2 ]; eassumption.
Qed.

Instance LR_FinCompTree {St A} : LR (FinCompTree St A) :=
  { lr_leq := extendsFCT; lr_PreOrder := _ }.


(***
 *** The Finite Trace Monad
 ***)

(* The finite trace monad *)
Definition FinTraceM St A := St -> FinCompTree St A.

(* Typeclass resolution mostly finds this instance for us *)
Instance ConstLR_FinTraceM St : ConstLR (FinTraceM St) :=
  Build_ConstLR _ _.

(* Bind on a computation tree, applying f after the computation terminates *)
Fixpoint bindFinTree {St A B} (fct: FinCompTree St A)
         (f : A -> FinTraceM St B) : FinCompTree St B :=
  match fct with
  | CompStuck => CompStuck
  | CompDone s a => f a s
  | CompStep s step =>
    CompStep s (fun s' => bindFinTree (step s') f)
  | CompChoice fct1 fct2 =>
    CompChoice (bindFinTree fct1 f) (bindFinTree fct2 f)
  end.

Instance Proper_bindFinTree St A B :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (@bindFinTree St A B).
Proof.
  admit. (* FIXME HERE *)
Admitted.

(* Build the computation that nondeterministically (via CompChoice) applies the
function f on some CompStep in fct *)
Fixpoint applyAtSomeStepFCT {St A B}
         (f: (St -> FinCompTree St A) -> (St -> FinCompTree St B))
         (fct: FinCompTree St A) : FinCompTree St B :=
  match fct with
  | CompStuck => CompStuck
  | CompDone s a => f (fun s' => CompDone s' a) s
  | CompStep s step =>
    CompChoice
      (CompStep s (f step))
      (CompStep s (fun s' => applyAtSomeStepFCT f (step s')))
  | CompChoice fct1 fct2 =>
    CompChoice (applyAtSomeStepFCT f fct1) (applyAtSomeStepFCT f fct2)
  end.

Fixpoint forkJoinFCT {St A B} (fct: FinCompTree St A)
         (mb: St -> FinCompTree St B) : FinCompTree St (A*B) :=
  match fct with
  | CompStuck => CompStuck
  | CompDone s a =>
    bindFinTree (mb s) (fun b s' => CompDone s' (a,b))
  | CompStep s step =>
    CompChoice
      (CompStep s (fun s' => forkJoinFCT (step s') mb))
      (CompStep
         s
         (fun s' =>
            applyAtSomeStepFCT
              (fun mb' s' => forkJoinFCT (step s') mb')
              (mb s)))
  | CompChoice fct1 fct2 =>
    CompChoice (forkJoinFCT fct1 mb) (forkJoinFCT fct2 mb)
  end.

Instance MonadTraceOps_FinTraceM St : MonadTraceOps (FinTraceM St) St :=
  {|
    returnM A a := fun s => CompDone s a;
    bindM A B m f := fun s => bindFinTree (m s) f;
    getM := fun s => CompDone s s;
    putM s := fun _ => CompDone s tt;
    yieldM := fun s => CompStep s (fun s => CompDone s tt);
  |}.

Instance MonadTrace_FinTraceM St : MonadTrace (FinTraceM St) St.
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadForkJoinOps_FinTraceM St : MonadForkJoinOps (FinTraceM St) :=
  {|
    forkJoinM :=
      fun A B m1 m2 s =>
        CompChoice
          (forkJoinFCT (m1 s) m2)
          (bindFinTree (forkJoinFCT (m2 s) m1)
                       (fun (ba:B*A) s' => CompDone s' (snd ba, fst ba)))
  |}.

Instance MonadForkJoin_FinTraceM St : MonadForkJoin (FinTraceM St).
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The Trace Monad
 ***)

Definition TraceM St A := DownSet (FinTraceM St A).

Instance ConstLR_TraceM St : ConstLR (TraceM St) := Build_ConstLR _ _.

Instance MonadTraceOps_TraceM St : MonadTraceOps (TraceM St) St :=
  {|
    returnM A a := downClose (returnM a);
    bindM A B m f :=
      bindDownSet m (fun fin_m =>
                       mapDownSet (bindM fin_m) (lambdaDownSet f));
    getM := downClose getM;
    putM s := downClose (putM s);
    yieldM := downClose yieldM
  |}.

Instance MonadTrace_TraceM St : MonadTrace (TraceM St) St.
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadForkJoinOps_TraceM St : MonadForkJoinOps (TraceM St) :=
  {|
    forkJoinM A B m1 m2 :=
      bindDownSet m1 (fun (fin_m1: FinTraceM St A) =>
                        mapDownSet (forkJoinM fin_m1) m2)
  |}.

Instance MonadForkJoin_TraceM St : MonadForkJoin (TraceM St).
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadFixOps_TraceM St : MonadFixOps (TraceM St) :=
  {|
    fixM A B lrA lrB f := fixDownSet f
  |}.

Instance MonadFix_TraceM St : MonadFix (TraceM St).
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The Continuation-Trace Monad
 ***)

Definition ContTraceM St A := (A -> TraceM St unit) -> TraceM St unit.

Instance ConstLR_ContTraceM St : ConstLR (ContTraceM St) := Build_ConstLR _ _.

Instance MonadTraceOps_ContTraceM St : MonadTraceOps (ContTraceM St) St :=
  {|
    returnM A a := fun k => k a;
    bindM A B m f := fun k => m (fun x => f x k);
    getM := fun k => bindM getM k;
    putM s := fun k => bindM (putM s) k;
    yieldM := fun k => bindM yieldM k;
  |}.

Instance MonadTrace_ContTraceM St : MonadTrace (ContTraceM St) St.
Proof.
  admit.
Admitted.

Instance MonadFixOps_ContTraceM St : MonadFixOps (ContTraceM St) :=
  {|
    fixM A B lrA lrB f a k :=
      fixDownSet (fun g ak => f (fun a' k' => g (a', k')) (fst ak) (snd ak)) (a,k)
  |}.

Instance MonadFix_ContTraceM St : MonadFix (ContTraceM St).
Proof.
  admit.
Admitted.

Instance MonadForkOps_ContTraceM St : MonadForkOps (ContTraceM St) :=
  {|
    forkM :=
      fun (m: ContTraceM St unit) =>
        (fun k =>
           bindM (forkJoinM (m returnM) (k tt)) (fun _ => returnM tt))
        : ContTraceM St unit
  |}.

Instance MonadFork_ContTraceM St : MonadFork (ContTraceM St).
Proof.
  admit.
Admitted.


(***
 *** Computation Traces in the Trace Monad
 ***)

Definition stepsTo1 {St A} `{LR A} : relation (St * TraceMonad St A) :=
  fun stm1 stm2 =>
    CompStepF (fst stm2) (snd stm2) <lr= (snd stm1) (fst stm1).

Definition stepsTo {St A} `{LR A} := clos_trans _ (stepsTo1 (St:=St) (A:=A)).

Definition evalsTo1 {St A} `{LR A} (stm : St * TraceMonad St A) (res : St * A) :=
  inDownSet ((snd stm) (fst stm)) (CompDone (fst res) (snd res)).

Definition evalsTo {St A} `{LR A} (stm : St * TraceMonad St A) (res : St * A) :=
  exists2 stm', stepsTo stm stm' & evalsTo1 stm' res.
