Require Export Coq.Relations.Relations.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Setoids.Setoid.


(***
 *** Logical Relations
 ***)

Class LR A : Type :=
  { lr_leq : relation A; lr_PreOrder :> PreOrder lr_leq }.

(* Typeclass resolution should not be filling in evars *)
Hint Mode LR ! : typeclass_instances.

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


(***
 *** Logical Relations for Common Types
 ***)

Instance LR_unit : LR unit := { lr_leq := fun _ _ => True }.
Proof.
  constructor; intro; intros; apply I.
Defined.

Instance LR_product {A B} `{LR A} `{LR B} : LR (A*B) :=
  { lr_leq := fun p1 p2 => fst p1 <lr= fst p2 /\ snd p1 <lr= snd p2 }.
Proof.
  constructor.
  - intro p. split; reflexivity.
  - intros p1 p2 p3 [ R12_l R12_r ] [ R23_l R23_r ].
    split; etransitivity; eassumption.
Defined.

(* The sort-of pointwise relation on sum types *)
Inductive sumR {A B} `{LR A} `{LR B} : A+B -> A+B -> Prop :=
| sumR_inl a1 a2 : a1 <lr= a2 -> sumR (inl a1) (inl a2)
| sumR_inr b1 b2 : b1 <lr= b2 -> sumR (inr b1) (inr b2).

Instance LR_sum {A B} `{LR A} `{LR B} : LR (A+B) :=
  { lr_leq := sumR; }.
Proof.
  constructor.
  - intro s. destruct s; constructor; reflexivity.
  - intros s1 s2 s3 R12 R23; destruct R12; inversion R23;
      constructor; etransitivity; eassumption.
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


(* The logical relation for provable equality *)
(* NOTE: we make this a Definition and *NOT* an Instance so that typeclass
resolution does not use it everywhere *)
Definition LR_eq {A} : LR A := {| lr_leq := eq |}.

(*
Class ConstLR (F : Type -> Type) : Type :=
  { lr_leq_K : forall {A}, LR (F A) }.

Instance LR_ConstLR F `{ConstLR F} A : LR (F A) := lr_leq_K.
Typeclasses Transparent LR_ConstLR.
*)

Class LRFunctor (F : forall A, LR A -> Type) : Type :=
  { lr_leq_F : forall {A} `{LR A}, LR (F A _) }.

Instance LR_LRFunctor F `{LRFunctor F} A `{LR A} : LR (F A _) := lr_leq_F.
Typeclasses Transparent LR_LRFunctor.

Class LRFunctor2 (F : forall A, LR A -> forall B, LR B -> Type) : Type :=
  { lr_leq_F2 : forall {A} `{LR A} {B} `{LR B}, LR (F A _ B _) }.

Instance LR_LRFunctor2 F `{LRFunctor2 F} A `{LR A} B `{LR B} : LR (F A _ B _) :=
  lr_leq_F2.
Typeclasses Transparent LR_LRFunctor2.


(***
 *** Some Useful Properness Instances for Rewriting
 ***)

Instance Proper_lr_equiv_lr_equiv A `{LR A} :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv) (@lr_equiv A _).
Proof.
  intros x1 x2 Rx y1 y2 Ry. split; intro.
  - rewrite <- Rx. rewrite <- Ry. assumption.
  - rewrite Rx. rewrite Ry. assumption.
Qed.

Instance Proper_pair A `{LR A} B `{LR B} :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (@pair A B).
Proof.
  intros a1 a2 Ra b1 b2 Rb. split; assumption.
Qed.

Instance Proper_pair_equiv A `{LR A} B `{LR B} :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv) (@pair A B).
Proof.
  intros a1 a2 Ra b1 b2 Rb. destruct Ra; destruct Rb; split; split; assumption.
Qed.
Instance Proper_fst A `{LR A} B `{LR B} :
  Proper (lr_leq ==> lr_leq) (@fst A B).
Proof.
  intros p1 p2 Rp. destruct Rp. assumption.
Qed.

Instance Proper_snd A `{LR A} B `{LR B} :
  Proper (lr_leq ==> lr_leq) (@snd A B).
Proof.
  intros p1 p2 Rp. destruct Rp. assumption.
Qed.

Instance Proper_fst_equiv A `{LR A} B `{LR B} :
  Proper (lr_equiv ==> lr_equiv) (@fst A B).
Proof.
  intros p1 p2 eqp. destruct eqp as [ [ Rp1 Rp2 ] [ Rp1' Rp2' ] ].
  split; assumption.
Qed.

Instance Proper_snd_equiv A `{LR A} B `{LR B} :
  Proper (lr_equiv ==> lr_equiv) (@snd A B).
Proof.
  intros p1 p2 eqp. destruct eqp as [ [ Rp1 Rp2 ] [ Rp1' Rp2' ] ].
  split; assumption.
Qed.

Instance Proper_and_equiv : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) and.
Proof.
  change (Proper (iff ==> iff ==> iff) and). typeclasses eauto.
Qed.

Instance Proper_or_equiv : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) or.
Proof.
  change (Proper (iff ==> iff ==> iff) or). typeclasses eauto.
Qed.


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

Instance Proper_fixDownSet {A B} `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq) (fixDownSet (A:=A) (B:=B)).
Proof.
  admit. (* FIXME HERE *)
Admitted.

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

Definition applyDownSet {A B} `{LR B} (dsF: DownSet (A -> B)) (a:A) : DownSet B :=
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
 *** Lenses
 ***)

(* A lens relating a "container" type A to a "component" type B *)
Record Lens (A B: Type) `{LR A} `{LR B} : Type :=
  {
    getL : A -> B;
    putL : B -> A -> A;
    proper_getL : Proper (lr_equiv ==> lr_equiv) getL;
    proper_putL : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) putL;
    lens_get_put : forall a, putL (getL a) a =lr= a;
    lens_put_get : forall a b, getL (putL b a) =lr= b;
    lens_put_put : forall a b1 b2, putL b2 (putL b1 a) =lr= putL b2 a;
  }.

Arguments getL {A B _ _} _ _.
Arguments putL {A B _ _} _ _ _.
Arguments lens_get_put {A B _ _}.
Arguments lens_put_get {A B _ _}.
Arguments lens_put_put {A B _ _}.

Instance Proper_getL St1 St2 `{LR St1} `{LR St2} (l: Lens St1 St2) :
  Proper (lr_equiv ==> lr_equiv) (getL l) :=
  proper_getL _ _ _.

Instance Proper_putL St1 St2 `{LR St1} `{LR St2} (l: Lens St1 St2) :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv) (putL l) :=
  proper_putL _ _ _.

(* FIXME HERE: define some standard lenses, e.g., identity, projections, etc.,
as well as composition of lenses *)


(***
 *** Monads With a Notion of Execution Traces
 ***)

(* The operations for a monad with execution traces *)
Class MonadTraceOps (M: forall St `{LR St} A `{LR A}, Type) : Type :=
  {
    (* Monadic return and bind *)
    returnM : forall {St} `{LR St} {A} `{LR A}, A -> M St A;
    bindM : forall {St} `{LR St} {A B} `{LR A} `{LR B},
        M St A -> (A -> M St B) -> M St B;

    (* State monad operations *)
    getM : forall {St} `{LR St}, M St St;
    putM : forall {St} `{LR St}, St -> M St unit;

    (* Perform a sub-computation in a restricted, component portion of the
    state, using a lens to define the relationship between state types *)
    restrictM : forall {St1 St2} `{LR St1} `{LR St2} {A} `{LR A},
        Lens St1 St2 -> M St2 A -> M St1 A;

    (* Perform a sub-computation in an expanded, container type, which must be
    initialized, and then throw away the rest of the container to keep just the
    component state *)
    expandM : forall {St1 St2} `{LR St1} `{LR St2} {A} `{LR A},
        Lens St2 St1 -> St2 -> M St2 A -> M St1 A;

    (* One-step evolution to a final or intermediate state *)
    stepsTo1 : forall {St} `{LR St} {A} `{LR A},
        St -> M St A -> St -> A + M St A -> Prop;
  }.

(* Evolution = stepping to an intermediate state *)
Definition evolvesTo1 `{MonadTraceOps} {St} `{LR St} {A} `{LR A}
           st1 (m1: M St _ A _) st2 m2 : Prop :=
  stepsTo1 st1 m1 st2 (inr m2).

(* Multi-step evolution *)
Definition evolvesTo `{MonadTraceOps} {St} `{LR St} {A} `{LR A}
           st1 (m1: M St _ A _) st2 m2 : Prop :=
  clos_refl_trans _ (fun st_m_1 st_m_2 =>
                       evolvesTo1 (fst st_m_1) (snd st_m_1)
                                  (fst st_m_2) (snd st_m_2))
                  (st1, m1) (st2, m2).

Definition stepsTo `{MonadTraceOps} {St} `{LR St} {A} `{LR A}
           st1 (m1: M St _ A _) st2 res : Prop :=
  match res with
  | inl a =>
    exists st2' m2, evolvesTo st1 m1 st2' m2 /\ stepsTo1 st2' m2 st2 (inl a)
  | inr m2 => evolvesTo st1 m1 st2 m2
  end.

Class MonadTrace (M: forall St `{LR St} A `{LR A}, Type)
      `{LRFunctor2 M} `{MonadTraceOps M} : Prop :=
  {
    (* Proper-ness requirements *)
    Proper_returnM {St} `{LR St} {A} `{LR A} :
      Proper (lr_leq ==> lr_leq) (returnM (M:=M) (A:=A));
    Proper_bindM {St} `{LR St} {A B} `{LR A} `{LR B} :
      Proper (lr_leq ==> lr_leq ==> lr_leq) (bindM (M:=M) (A:=A) (B:=B));
    Proper_putM {St} `{LR St} : Proper (lr_leq ==> lr_leq) (putM (M:=M));
    Proper_stepsTo1 {St} `{LR St} {A} `{LR A} :
      Proper (lr_equiv ==> lr_equiv ==> lr_equiv ==> lr_equiv ==> lr_equiv)
             (stepsTo1 (M:=M) (A:=A));

    (* FIXME: need to connect stepsTo1 more closely with the LR; e.g., if
    stepsTo1 st1 m1 st2 res and m1 <lr= m2 then there should be some res2 such
    that res1 <lr= res2 and stepsTo1 st1 m2 st2 res2, but maybe with extended
    st1 and st2...? Is it like bisimulation, where extending either of (st1,m)
    or (st2,res) yields an extended other one such that stepsTo1 still holds? *)

    (* Standard monad laws, which require bind functions to be Proper *)
    monad_return_bind {St} `{LR St} {A B} `{LR A} `{LR B} a (f : A -> M St B) :
      Proper (lr_leq ==> lr_leq) f ->
      bindM (returnM a) f =lr= f a;
    monad_bind_return {St} `{LR St} {A} `{LR A} (m : M St A) :
      bindM m returnM =lr= m;
    monad_assoc {St} `{LR St} {A B C} `{LR A} `{LR B} `{LR C}
                m (f: A -> M St B) (g: B -> M St C) :
      Proper (lr_leq ==> lr_leq) f ->
      Proper (lr_leq ==> lr_leq) g ->
      bindM (bindM m f) g =lr= bindM m (fun x => bindM (f x) g);

    (* FIXME: write the state monad laws! *)

    (* FIXME: write the monad laws for restrictM and expandM *)

    (* Laws for stepsTo1 *)
    stepsTo1_returnM {St} `{LR St} {A} `{LR A} (a:A) st :
      stepsTo1 st (returnM a) st (inl a);
    stepsTo1_bindM_1{St} `{LR St}  {A B} `{LR A} `{LR B}
                           st st' (m1 m2: M St A) (f: A -> M St B) :
      Proper (lr_leq ==> lr_leq) f ->
      stepsTo1 st m1 st' (inr m2) ->
      stepsTo1 st (bindM m1 f) st' (inr (bindM m2 f));
    stepsTo1_bindM_2 {St} `{LR St} {A B} `{LR A} `{LR B}
                     st st' st'' (m1: M St A) a (f: A -> M St B) res :
      Proper (lr_leq ==> lr_leq) f ->
      stepsTo1 st m1 st' (inl a) -> stepsTo1 st' (f a) st'' res ->
      stepsTo1 st (bindM m1 f) st' res;
    stepsTo1_getM {St} `{LR St} (st:St) : stepsTo1 st getM st (inl st);
    stepsTo1_putM {St} `{LR St} (st st':St) : stepsTo1 st (putM st') st' (inl tt);

    (* FIXME: write the stepsTo1 laws for restrictM and expandM *)
  }.


(* Monads that support parallel execution of a process *)
Class MonadParallelOps (M: forall St `{LR St} A `{LR A}, Type) : Type :=
  {
    parallelM {St} `{LR St} {A} `{LR A} : M St A -> M St unit -> M St A;
    yieldM {St} `{LR St} : M St unit;
  }.

Class MonadParallel (M: forall St `{LR St} A `{LR A}, Type)
      `{LRFunctor2 M} `{MonadTraceOps M} `{MonadParallelOps M} : Prop :=
  {
    (* MonadParallel is a subclass of MonadTrace *)
    MonadTrace_MonadParallel :> MonadTrace M;

    (* parallelM is Proper *)
    Proper_parallelM {St} `{LR St} :
      Proper (lr_leq ==> lr_leq ==> lr_leq) (parallelM (St:=St) (M:=M));

    (* parallelM commutes with bindM *)
    bindM_parallelM {St} `{LR St} {A B} `{LR A} `{LR B} m1 m2 f :
      Proper (lr_leq ==> lr_leq) f ->
      bindM (parallelM (St:=St) (M:=M) m1 m2) f =lr= parallelM (bindM m1 f) m2;

    (* Laws for stepsTo1 *)
    (* NOTE: there is no case for parallelM m1 m2 where m1 returns a value,
    because this implies that m1 contains no yields, and so cannot be
    interrupted anywhere. This is a little unintuitive, but makes sense if you
    think about it a certain way... *)
    stepsTo1_yieldM {St} `{LR St} (st:St) :
      stepsTo1 st (yieldM (M:=M)) st (inr (returnM tt));
    stepsTo1_parallelM_1 {St} `{LR St} (st st':St) m1 m1' m2 :
      stepsTo1 st m1 st' (inr m1') ->
      stepsTo1 st (parallelM m1 m2) st' (inr (parallelM m1 m2));
    stepsTo1_parallelM_2 {St} `{LR St} (st st':St) m1 m2 m2' :
      stepsTo1 st m2 st' (inr m2') ->
      stepsTo1 st (parallelM m1 m2) st' (inr (parallelM m1 m2'));
    stepsTo1_parallelM_3 {St} `{LR St} (st st':St) m1 m2 :
      stepsTo1 st m2 st' (inl tt) ->
      stepsTo1 st (parallelM m1 m2) st' (inr m1);
  }.


Class MonadFixOps (M: forall St `{LR St} A `{LR A}, Type) : Type :=
  {
    fixM : forall {St} `{LR St} {A B} `{LR A} `{LR B},
      ((A -> M St B) -> (A -> M St B)) -> A -> M St B;
  }.

Class MonadFix (M: forall St `{LR St} A `{LR A}, Type)
      `{LRFunctor2 M} `{MonadFixOps M} : Prop :=
  {
    Proper_fixM {St} `{LR St} {A B} `{LR A} `{LR B} :>
      Proper (lr_leq ==> lr_leq) (fixM (St:=St) (M:=M) (A:=A) (B:=B));
    fixM_correct :
      forall {St} `{LR St} {A B} `{LR A} `{LR B}
             (f: (A -> M St B) -> (A -> M St B)),
        Proper (lr_leq ==> lr_leq) f ->
        fixM f =lr= f (fixM f)
  }.


(***
 *** The Standard State Monad as a Trace Monad
 ***)

Definition StateM St `{LR St} A `{LR A} := St -> St * A.

Instance LRFunctor2_StateM : LRFunctor2 StateM :=
  Build_LRFunctor2 _ _.

Instance MonadTraceOps_StateM : MonadTraceOps StateM :=
  {|
    returnM St lrSt A lrA a st := (st, a);
    bindM St lrSt A B lrA lrB m f st :=
      let (st', a) := m st in
      f a st';
    getM St lrSt st := (st, st);
    putM St lrSt st' st := (st', tt);

    restrictM St1 St2 lrSt1 lrSt2 A lrA l m st1 :=
      let (st2', a) := m (getL l st1) in
      (putL l st2' st1, a);

    expandM St1 St2 lrSt1 lrSt2 A lrA l st2 m st1 :=
      let (st2', a) := m (putL l st1 st2) in
      (getL l st2', a);
    
    stepsTo1 St lrSt A lrA st1 m st2 res :=
      st2 = fst (m st1) /\ res = inl (snd (m st1));
  |}.

Instance MonadTrace_StateM : MonadTrace StateM.
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The State Monad + Fixed-Points
 ***)

(* FIXME HERE: this needs an Option A in the output type, along with the
appropriate LR; maybe call that type Bottom A instead of Option A? *)
Definition FixStateM St `{LR St} A `{LR A} := DownSet (StateM St A).

Instance LRFunctor_FixStateM : LRFunctor2 FixStateM :=
  Build_LRFunctor2 _ _.

Instance MonadTraceOps_FixStateM : MonadTraceOps FixStateM :=
  {|
    returnM St lrSt A lrA a := downClose (returnM a);
    bindM St lrSt A B lrA lrB m f :=
      bindDownSet
        m (fun m' =>
             bindDownSet (lambdaDownSet f) (fun f' => downClose (bindM m' f')));
    getM St lrSt := downClose getM;
    putM St lrSt st' := downClose (putM (M:=StateM) st');

    restrictM St1 St2 lrSt1 lrSt2 A lrA l m :=
      mapDownSet (restrictM l) m;
    expandM St1 St2 lrSt1 lrSt2 A lrA l st2 m :=
      mapDownSet (expandM l st2) m;

    stepsTo1 St lrSt A lrA st1 m st2 res :=
      match res with
      | inl a =>
        exists m', inDownSet m m' /\ stepsTo1 st1 m' st2 (inl a)
      | inr res_m =>
        exists m' res_m',
        inDownSet m m' /\ inDownSet res_m res_m' /\
        stepsTo1 st1 m' st2 (inr res_m')
      end;
  |}.

Instance MonadTrace_FixStateM : MonadTrace FixStateM.
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** Finite Computation Trees
 ***)

Inductive FinCompTree St A : Type :=
| CompStuck
| CompDone (s:St) (a:A)
| CompStep (s:St) (m: St -> FinCompTree St A)
| CompPar (m: FinCompTree St A) (m2: FinCompTree St unit)
.

Arguments CompStuck {St A}.
Arguments CompDone {St A} s a.
Arguments CompStep {St A} s m.
Arguments CompPar {St A} m m2.

Fixpoint extendsFCT {St A} `{LR St} `{LR A} (t1 t2 : FinCompTree St A) : Prop :=
  match (t1, t2) with
  | (CompStuck, _) => True
  | (CompDone s1 a1, CompDone s2 a2) => s1 <lr= s2 /\ a1 <lr= a2
  | (CompStep s1 m1, CompStep s2 m2) =>
    s1 <lr= s2 /\ forall s, extendsFCT (m1 s) (m2 s)
  | (CompPar m1 m1', CompPar m2 m2') =>
    extendsFCT m1 m2 /\ extendsFCT m1' m2'
  | _ => False
  end.

Instance PreOrder_extendsFCT {St A} `{LR St} `{LR A} :
  PreOrder (extendsFCT (St:=St) (A:=A)).
Proof.
  constructor.
  - intros tree; induction tree; simpl; auto; split; try reflexivity.
    intros; apply H1.
  - intros tree1; induction tree1;
      intros tree2 tree3;
      destruct tree2; destruct tree3; simpl; intros R12 R23;
        try auto; try contradiction.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23 | rewrite Ra12; rewrite Ra23 ];
        reflexivity.
    + destruct R12 as [ Rs12 Ra12 ]; destruct R23 as [ Rs23 Ra23 ].
      split; [ rewrite Rs12; rewrite Rs23; reflexivity | ].
      intro. apply (H1 _ _ _ _ (Ra12 _) (Ra23 _)).
    + destruct R12 as [ R12_1 R12_2 ]; destruct R23 as [ R23_1 R23_2 ].
      split; [ eapply IHtree1_1 | eapply IHtree1_2 ]; eassumption.
Qed.

Instance LR_FinCompTree {St A} `{LR St} `{LR A} : LR (FinCompTree St A) :=
  { lr_leq := extendsFCT; lr_PreOrder := _ }.


(***
 *** The Finite Trace Monad
 ***)

(* The finite trace monad *)
Definition FinTraceM St `{LR St} A `{LR A} := St -> FinCompTree St A.

(* Typeclass resolution mostly finds this instance for us *)
Instance LRFunctor2_FinTraceM : LRFunctor2 FinTraceM :=
  Build_LRFunctor2 _ _.

(* Bind on a computation tree, applying f after the computation terminates *)
Fixpoint bindFinTree {St} `{LR St} {A B} `{LR B} (fct: FinCompTree St A)
         (f : A -> FinTraceM St B) : FinCompTree St B :=
  match fct with
  | CompStuck => CompStuck
  | CompDone s a => f a s
  | CompStep s step =>
    CompStep s (fun s' => bindFinTree (step s') f)
  | CompPar fct1 fct2 => CompPar (bindFinTree fct1 f) fct2
  end.

Instance Proper_bindFinTree St A B `{LR St} `{LR A} `{LR B} :
  Proper (lr_leq ==> lr_leq ==> lr_leq) (bindFinTree (St:=St) (A:=A) (B:=B)).
Proof.
  admit. (* FIXME HERE *)
Admitted.

(* Map the intermediate states in a finite tree to another state type, using
"from" and "to" functions *)
Fixpoint mapFinTree {St1 St2} `{LR St1} `{LR St2} {A} `{LR A}
         (f_to: St1 -> St2) (f_from: St2 -> St1) (fct: FinCompTree St1 A) :
  FinCompTree St2 A :=
  match fct with
  | CompStuck => CompStuck
  | CompDone st a => CompDone (f_to st) a
  | CompStep st step =>
    CompStep (f_to st) (fun st' => mapFinTree f_to f_from (step (f_from st')))
  | CompPar fct1 fct2 =>
    CompPar (mapFinTree f_to f_from fct1) (mapFinTree f_to f_from fct2)
  end.

Instance Proper_mapFinTree St1 St2 A `{LR St1} `{LR St2} `{LR A} f_to f_from :
  Proper (lr_leq ==> lr_leq) (mapFinTree (St1:=St1) (St2:=St2) f_to f_from).
Proof.
  admit. (* FIXME HERE *)
Admitted.

(* States that fct steps to output state st and remaining computation m *)
Fixpoint stepFinTree {St A B} `{LR St} `{LR A} `{LR B}
         (fct: FinCompTree St A) st m : Prop :=
  match fct with
  | CompStuck => False
  | CompDone _ _ => False
  | CompStep st' m' => st =lr= st' /\ m' =lr= m
  | CompPar fct1 fct2 =>
    (exists m', stepFinTree fct1 st m' /\ m = fun st' => CompPar (m' st') fct2)
    \/
    (exists m', stepFinTree fct2 st m' /\ m = fun st' => CompPar fct1 (m' st'))
  end.


Instance MonadTraceOps_FinTraceM : MonadTraceOps FinTraceM :=
  {|
    returnM St lrSt A lrA a := fun s => CompDone s a;
    bindM St lrSt A B lrA lrB m f s := bindFinTree (m s) f;
    getM St lrSt st := CompDone st st;
    putM St lrSt st' st := CompDone st' tt;
    restrictM St1 St2 lrSt1 lrSt2 A lrA l m st1 :=
      mapFinTree (fun st2 => putL l st2 st1) (getL l) (m (getL l st1));
    expandM St1 St2 lrSt1 lrSt2 A lrA l st2 m st1 :=
      mapFinTree (getL l) (fun st1' => putL l st1' st2) (m (putL l st1 st2));
    stepsTo1 St lrSt A lrA st1 m1 st2 res :=
      match res with
      | inl a => m1 st1 =lr= CompDone st2 a
      | inr m2 => stepFinTree (m1 st1) st2 m2
      end
  |}.

Instance MonadTrace_FinTraceM : MonadTrace FinTraceM.
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadParallelOps_FinTraceM : MonadParallelOps FinTraceM :=
  {|
    parallelM St lrSt A lrA m1 m2 st :=
      CompPar (m1 st : FinCompTree St A) (m2 st);
    yieldM St lrSt s := CompStep s (fun s => CompDone s tt);
  |}.

Instance MonadParallel_FinTraceM : MonadParallel FinTraceM.
Proof.
  admit. (* FIXME HERE *)
Admitted.


(***
 *** The Trace Monad
 ***)

Definition TraceM St `{LR St} A `{LR A} := DownSet (FinTraceM St A).

Instance LRFunctor2_TraceM : LRFunctor2 TraceM :=
  Build_LRFunctor2 _ _.

Instance MonadTraceOps_TraceM : MonadTraceOps TraceM :=
  {|
    returnM St lrSt A lrA a := downClose (returnM a);
    bindM St lrSt A B lrA lrB m f :=
      bindDownSet m (fun fin_m =>
                       mapDownSet (bindM fin_m) (lambdaDownSet f));
    getM St lrSt := downClose getM;
    putM St lrSt s := downClose (putM (M:=FinTraceM) s);

    restrictM St1 St2 lrSt1 lrSt2 A lrA l m :=
      mapDownSet (restrictM l) m;
    expandM St1 St2 lrSt1 lrSt2 A lrA l st2 m :=
      mapDownSet (expandM l st2) m;
    
    stepsTo1 St lrSt A lrA st1 m1 st2 res :=
      match res with
      | inl a =>
        exists fin_m, inDownSet m1 fin_m /\ stepsTo1 st1 fin_m st2 (inl a)
      | inr m2 =>
        (* m2 must be non-empty *)
        (exists fin_m2, inDownSet m2 fin_m2) /\
        (* Every element of m2 must have an element of m1 that steps to it *)
        forall fin_m2,
          inDownSet m2 fin_m2 ->
          exists fin_m1,
            inDownSet m1 fin_m1 /\ stepsTo1 st1 fin_m1 st2 (inr fin_m2)
      end
  |}.

Instance MonadTrace_TraceM : MonadTrace TraceM.
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadFixOps_TraceM : MonadFixOps TraceM :=
  {|
    fixM St lrSt A B lrA lrB := fixDownSet
  |}.

Instance MonadFix_TraceM : MonadFix TraceM.
Proof.
  admit. (* FIXME HERE *)
Admitted.

Instance MonadParallelOps_TraceM : MonadParallelOps TraceM :=
  {|
    parallelM St lrSt A lrA m1 m2 :=
      bindDownSet
        (m1 : TraceM St A)
        (fun fin_m1 =>
           bindDownSet m2 (fun fin_m2 =>
                             downClose (parallelM fin_m1 fin_m2)));
    yieldM St lrSt := downClose yieldM;
  |}.

Instance MonadParallel_TraceM : MonadParallel TraceM.
Proof.
  admit. (* FIXME HERE *)
Admitted.
