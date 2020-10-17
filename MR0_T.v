Require Import Bool.
Require Export MR0_D.
Require Export MR0_L.

Section DerivedProperties.

Variable l : blocklist.

(** The current system state satisfy  I_1:clh=0 *)
Hypothesis list_from_zero_current : list_from_zero l = true.

(*allocate: list_from_zero*)
Theorem allocate_list_from_zero : forall(r: nat),
  list_from_zero (allocate r l) = true.
Proof.
  intros. unfold list_from_zero; simpl.
  rewrite <- bl_end_allocate_equal.
  apply lfr_equal_bfr in list_from_zero_current. 
  case (allocate r l); simpl.
  - reflexivity.
  - intros. assumption. Qed.

(*release: list_from_zero
Theorem release_list_from_zero : forall (b: Block),
  busy_block_in_list b l -> 
  list_from_zero (release b l) = true.
Proof.
Proof. (* FILL IN HERE *) Admitted.
*)


(** The current system state satisfy  I_6:*)
Hypothesis list_from_zero_current : list_from_zero l = true.
(*allocate2 : list_not_gap*)
Theorem allocate_list_not_gap : forall (l: blocklist) (r: nat),
  list_not_gap l = true -> list_not_gap (allocate r l) = true.
Proof.
  intros. induction l.
  - unfold allocate. simpl. case r; simpl; try (intros; reflexivity). assumption.
    assert (H1: list_not_gap (allocate r (b :: l)) = list_not_gap (allocate r l)).
    { apply (lng_relate_allocate l r b). assumption. }
    rewrite H1. apply lng_equal_minus in H. apply IHl in H. assumption. Qed.

(*allocate3 : list_not_zeroB*)
Theorem allocate_list_not_zeroB : forall (l: blocklist) (r: nat),
  list_not_zeroB l = true -> list_not_zeroB (allocate r l) = true.
Proof.
  intros. induction l.
  - unfold allocate; simpl. case r; simpl; try (intros; reflexivity).
  - assert (H1: list_not_zeroB (allocate r (b :: l)) = list_not_zeroB (allocate r l)).
    { apply (lnz_relate_allocate l r b). assumption. }
    rewrite H1. apply lnz_equal_minus in H. apply IHl in H. assumption. Qed.

(*release1 : list_from_zero*)
Theorem release_list_from_zero : forall (l: blocklist) (b: Block),
  list_from_zero l = true -> list_from_zero (release b l) = true.
Proof.
  intros. unfold list_from_zero. unfold release.
  
Proof. (* FILL IN HERE *) Admitted.

(*release2 : list_not_gap*)
Theorem release_list_not_gap : forall (l: blocklist) (b: Block),
  list_not_gap l = true -> list_not_gap (release b l) = true.
Proof. (* FILL IN HERE *) Admitted.

(*release3 : list_not_zeroB*)
Theorem release_list_not_zeroB : forall (l: blocklist) (b: Block),
  list_not_zeroB l = true -> list_not_zeroB (release b l) = true.
Proof. (* FILL IN HERE *) Admitted.



