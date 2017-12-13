Require Export BisimRefinement.TraceMonad.

(* An (St1,St2)-bisimulation permission is:

  1. The ability to read either St1 or St2 as an element of the other type,
     given by the relation R between the two types that intuitively describes
     the "information" you get from reading St1 as an St2 by describing the set
     of elements St2 you "see" when reading a particular element of St1; AND

  2. The ability to update either St1 or St2, given by a preorder on (St1 * St2)
     that describes the allowed updates to St1 along with corresponding updates
     to St2 that have to be made to "match" those updates to St1.

 *)
Record BPerm St1 St2 `{LR St1} `{LR St2} : Type :=
  {
    bperm_R : St1 -> St2 -> Prop;
    bperm_upd : relation (St1 * St2);

    proper_bperm_R : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) bperm_R;
    proper_bperm_upd : Proper (lr_equiv ==> lr_equiv ==> lr_equiv) bperm_upd;
    preorder_bperm_upd : PreOrder bperm_upd;
  }.

Arguments bperm_R {St1 St2 _ _}.
Arguments bperm_upd {St1 St2 _ _}.

Instance Proper_bperm_R_equiv St1 St2 `{LR St1} `{LR St2} (bperm: BPerm St1 St2) :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv) (bperm_R bperm) :=
  proper_bperm_R _ _ _.

Instance Proper_bperm_R St1 St2 `{LR St1} `{LR St2} (bperm: BPerm St1 St2) :
  Proper (lr_equiv ==> lr_equiv ==> Basics.impl) (bperm_R bperm).
Proof.
  intros st1 st1' eq1 st2 st2' eq2 R12.
  apply (proper_bperm_R _ _ bperm st1 st1' eq1 st2 st2' eq2). assumption.
Qed.

Instance Proper_bperm_upd_equiv St1 St2 `{LR St1} `{LR St2} (bperm: BPerm St1 St2) :
  Proper (lr_equiv ==> lr_equiv ==> lr_equiv) (bperm_upd bperm) :=
  proper_bperm_upd _ _ _.

Instance Proper_bperm_upd St1 St2 `{LR St1} `{LR St2} (bperm: BPerm St1 St2) :
  Proper (lr_equiv ==> lr_equiv ==> Basics.impl) (bperm_upd bperm).
Proof.
  intros st1 st1' eq1 st2 st2' eq2 R12.
  apply (proper_bperm_upd _ _ bperm st1 st1' eq1 st2 st2' eq2). assumption.
Qed.

Instance PreOrder_bperm_upd St1 St2 `{LR St1} `{LR St2} (bperm: BPerm St1 St2) :
  PreOrder (bperm_upd bperm) := preorder_bperm_upd _ _ _.


(***
 *** Examples of Bisimulation Perms
 ***)

(* The trivial permission, that does not allow any updates *)
Program Definition trivial_bperm {St1 St2} `{LR St1} `{LR St2} : BPerm St1 St2 :=
  {|
    bperm_R st1 st2 := True;
    bperm_upd := lr_equiv;
  |}.
Next Obligation.
  intros st1 st1' eq1 st2 st2' eq2. reflexivity.
Defined.


(* Conjoin two permissions building the permission that allows updates from
either permission *)
Program Definition conjoin_bperms {St1 St2} `{LR St1} `{LR St2}
        (bperm1 bperm2: BPerm St1 St2) : BPerm St1 St2 :=
  {|
    bperm_R st1 st2 := bperm_R bperm1 st1 st2 /\ bperm_R bperm2 st1 st2;
    bperm_upd :=
      clos_refl_trans
        _ (fun st12 st12' =>
             bperm_upd bperm1 st12 st12' \/ bperm_upd bperm2 st12 st12');
  |}.
Next Obligation.
  intros st1 st1' eq1 st2 st2' eq2. rewrite eq1. rewrite eq2. reflexivity.
Defined.
Next Obligation.
  intros st1 st1' eq1 st2 st2' eq2.
  (*
  split; intro R12; induction R12.
  - apply rt_step. destruct H1; [ left | right ].
    + eapply Proper_bperm_upd; try symmetry; try eassumption.
    + eapply Proper_bperm_upd; try symmetry; try eassumption.
  - apply rt_step. left. eapply Proper_bperm_upd; try symmetry; try eassumption.
    reflexivity.
  - *)
  admit. (* FIXME HERE *)
Admitted.
Next Obligation.
  constructor.
  - intro. constructor. left; reflexivity.
  - intros st1 st2 st3 upd12 upd23.
    eapply rt_trans; eassumption.
Defined.


(* Composition of permissions *)
Program Definition compose_bperms {St1 St2 St3} `{LR St1} `{LR St2} `{LR St3}
        (bperm1: BPerm St1 St2) (bperm2: BPerm St2 St3) : BPerm St1 St3 :=
  {|
    bperm_R st1 st3 :=
      exists st2, bperm_R bperm1 st1 st2 /\ bperm_R bperm2 st2 st3;
    bperm_upd st13 st13' :=
      forall st2, exists st2',
          bperm_upd bperm1 (fst st13, st2) (fst st13', st2') /\
          bperm_upd bperm2 (st2, snd st13) (st2', snd st13')
  |}.
Next Obligation.
  intros st1 st1' eq1 st3 st3' eq3.
  split; intros [ st2 [ R12 R23 ]]; exists st2.
  - rewrite <- eq1; rewrite <- eq3. split; assumption.
  - rewrite eq1; rewrite eq3. split; assumption.
Defined.
Next Obligation.
  intros st13_1 st13_1' eq1 st13_2 st13_2' eq2.
  split; intros R_12 st2; destruct (R_12 st2) as [ st2' [R12 R23]]; exists st2'.
  - split; rewrite <- eq1; rewrite <- eq2; assumption.
  - split; rewrite eq1; rewrite eq2; assumption.
Defined.
Next Obligation.
  constructor.
  - intros st13 st2. exists st2. split; reflexivity.
  - intros st_1 st_2 st_3 R12 R23 st2.
    destruct (R12 st2) as [ st2' [R12_1 R12_2]].
    destruct (R23 st2') as [ st2'' [R23_1 R23_2]].
    exists st2''. split; etransitivity; eassumption.
Defined.


(* A lens is a BPerm, where get defines the read and put defines the update. Get
goes from left (the "bigger" type) to right (the "smaller" type) *)
Program Definition lens_bperm {St1 St2} `{LR St1} `{LR St2} (l: Lens St1 St2) :
  BPerm St1 St2 :=
  {|
    bperm_R st1 st2 := getL l st1 =lr= st2;
    bperm_upd st12 st12' :=
      (* This says we can change the smaller type any way at all, while we can
      only change the bigger type using put *)
      (snd st12 =lr= snd st12') /\
      (exists st2, putL l st2 (fst st12) =lr= fst st12');
  |}.
Next Obligation.
  intros st1 st1' eq1 st2 st2' eq2. rewrite eq1. rewrite eq2. reflexivity.
Defined.
Next Obligation.
  intros st1 st1' eq1 st2 st2' eq2. rewrite eq1.
  split; intros [ eq_snd [ st2'' eq_fst ]]; split.
  - rewrite <- eq2; assumption.
  - exists st2''. rewrite <- eq1. rewrite <- eq2. assumption.
  - rewrite eq2; assumption.
  - exists st2''. rewrite eq1. rewrite eq2. assumption.
Defined.
Next Obligation.
  constructor.
  - intros [ st1 st2 ]. split; [ reflexivity | ].
    exists (getL l st1). apply lens_get_put.
  - intros [ st1_1 st2_1 ] [ st1_2 st2_2 ] [ st1_3 st2_3 ]
           [ eq12 [st2_12 ] ] [ eq23 [st2_23 ] ].
    split; [ etransitivity; eassumption | ].
    exists st2_23. rewrite <- H1 in H2. etransitivity; [ | apply H2 ].
    rewrite lens_put_put. reflexivity.
Defined.


(***
 *** Separability of Permissions
 ***)

Definition bperms_separable {St1 St2} `{LR St1} `{LR St2}
           (bperm1 bperm2: BPerm St1 St2) : Prop :=
  (* Updates with bperm2 do not mess up the R of bperm1 *)
  (forall st1 st2 st1' st2',
      bperm_R bperm1 st1 st2 ->
      bperm_upd bperm2 (st1,st2) (st1',st2') ->
      bperm_R bperm1 st1' st2')
  /\
  (* Updates with bperm1 do not mess up the R of bperm2 *)
  (forall st1 st2 st1' st2',
      bperm_R bperm2 st1 st2 ->
      bperm_upd bperm1 (st1,st2) (st1',st2') ->
      bperm_R bperm2 st1' st2')
  /\
  (* The updates commute with each other *)
  (forall st1 st2 st1' st2',
      (exists st1'' st2'',
          bperm_upd bperm1 (st1,st2) (st1'',st2'') /\
          bperm_upd bperm2 (st1'',st2'') (st1',st2'))
      <->
      (exists st1'' st2'',
          bperm_upd bperm2 (st1,st2) (st1'',st2'') /\
          bperm_upd bperm1 (st1'',st2'') (st1',st2'))).

(* FIXME HERE: lemmas about permissions that are separable *)
