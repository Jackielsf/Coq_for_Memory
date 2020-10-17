Require Import Bool.
Require Export MR0_D.

(*Block*)
(*** ===========================================================*)
Lemma surjective_block : forall (b : Block),
  b = (bflag b, badd b, bsize b).
Proof.
  intros b. destruct b as [f a s]. simpl. reflexivity. Qed.

Hint Resolve surjective_block: memorymanage.

(**BlockList*)
(*** ===========================================================*)
(*BlockList --- app*)
Lemma appbl_nil_r : forall l : blocklist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| b l'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Lemma appbl_assoc : forall l1 l2 l3 : blocklist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity. Qed.

Hint Resolve appbl_nil_r appbl_assoc: memorymanage.

(*BlockList --- rev*)
Lemma rev_appbl_distr: forall l1 l2 : blocklist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1 as [| b l1'].
  - simpl. rewrite -> appbl_nil_r. reflexivity.
  - simpl. rewrite -> IHl1'. rewrite -> appbl_assoc. reflexivity. Qed.

Lemma rev_block_l : forall b : Block, forall l : blocklist,
  rev ([b] ++ l) = rev (l) ++ [b].
Proof.
  intros b l. induction l as [| a l'].
  - simpl. reflexivity.
  - simpl. reflexivity. Qed.

Lemma rev_block_r : forall b : Block, forall l : blocklist,
  rev (l ++ [b]) = b :: rev (l).
Proof.
  intros b l. induction l as [| a l'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHl'. reflexivity. Qed.

Lemma rev_involutive : forall l : blocklist,
  rev (rev l) = l.
Proof.
  intros l. induction l as [| b l'].
  - reflexivity.
  - simpl. rewrite -> rev_block_r. rewrite -> IHl'. reflexivity. Qed.

Hint Resolve rev_appbl_distr rev_block_l rev_block_r rev_involutive: memorymanage.

(*BlockList --- bl_end*)
Lemma bl_end_add : forall (l : blocklist) (b1 b2:Block),
  bl_end (b1 :: l) = bl_end (b2 :: b1 :: l).
Proof.
  intros l b1 b2. unfold bl_end; simpl. case (rev l); simpl.
  - reflexivity.
  - intros. reflexivity. Qed.

Hint Resolve bl_end_add: memorymanage.

(**some compute*)
(*** ===========================================================*)
Lemma eqb_refl : forall n : nat,
   (n =? n) = true.
Proof.
  intros n. induction n as [| n'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma eqblock_refl : forall (b: Block),
  eqblock b b = true.
Proof.
  intros. destruct b. unfold eqblock. rewrite eqb_refl.
  rewrite eqb_refl. reflexivity. Qed.

Lemma eqblocklist_refl : forall (l: blocklist),
  eqblocklist l l = true.
Proof.
  intros. induction l. 
  - simpl. reflexivity.
  - simpl. rewrite eqblock_refl. assumption. Qed.

Lemma eqblock_bust_to_free : forall (b: Block),
  eqblock b (bust_to_free b) = true.
Proof.
  intros. destruct b. unfold bust_to_free; simpl. case flag; unfold eqblock; 
  rewrite eqb_refl; rewrite eqb_refl; reflexivity. Qed.

Hint Resolve eqb_refl eqblock_refl eqblocklist_refl eqblock_bust_to_free: memorymanage.
(*eqblock b0 (bust_to_free b0)*)
(**allocate*)
(*** ===========================================================*)
Lemma allocate_0 : forall (l: blocklist),
  allocate 0 l = l.
Proof.
  intros. simpl. reflexivity. Qed.

Hint Resolve allocate_0: memorymanage.

(**allocate-list_from_zero*)
(*** ===========================================================*)
Lemma lfr_equal_bfr :  forall (l: blocklist),
  list_from_zero l = true -> block_from_zero (bl_end l) = true.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - simpl in H. destruct H. reflexivity. Qed.

Lemma bl_end_allocate_equal : forall (l: blocklist)(r: nat),
  block_from_zero (bl_end l) = block_from_zero (bl_end (allocate r l)).
Proof.
  intros. induction l.
  - simpl. unfold allocate, bl_end, block_from_zero; simpl. case r; simpl.
    + reflexivity.
    + intros; reflexivity.
  - unfold allocate; simpl. case r; simpl.
    + reflexivity.
    + case b; simpl. intros. rewrite <- bl_end_add. reflexivity. Qed.

(**allocate-list_not_gap *)
(*** ===========================================================*)

Lemma lng_relate_bfl : forall (b: Block)(l: blocklist),
  block_form_list b l = true -> list_not_gap l = true -> list_not_gap (b :: l) = true.
Proof.
  intros. unfold list_not_gap. rewrite H. apply H0. Qed.

Lemma lng_equal_minus : forall (b: Block)(l: blocklist),
  list_not_gap (b :: l) = true -> list_not_gap l = true.
Proof.
  intros. unfold list_not_gap in H. case (block_form_list b l) in H.
  fold list_not_gap in H; assumption. discriminate. Qed.

Lemma lng_relate_minus_bfl : forall (b: Block)(l: blocklist),
  list_not_gap (b :: l) = true -> block_form_list b l = true.
Proof.
  intros. assert (H1: list_not_gap l = true). { apply lng_equal_minus in H; apply H. }
  elim H. unfold list_not_gap. case (block_form_list b l); simpl.
  - symmetry. apply H1.
  - reflexivity. Qed.

Lemma lng_equal_app : forall (b1 b2: Block)(l: blocklist),
  (badd b1 =? (badd b2) + (bsize b2)) = true -> 
  list_not_gap (b2 :: l) = list_not_gap (b1 :: b2 :: l).
Proof.
  intros. induction l.
  - simpl. rewrite H. reflexivity.
  - unfold list_not_gap, block_form_list. rewrite H. reflexivity. Qed.

(*add about plus*)
Lemma plus_n_m: forall n m : nat, (n + m =? n + m) = true.
Proof.
  intros. induction n. 
  - simpl. apply eqb_refl; reflexivity. 
  - simpl. assumption. Qed.

Lemma lng_relate_allocate : forall (l: blocklist)(r: nat)(b: Block),
  list_not_gap (b :: l) = true ->
    list_not_gap (allocate r (b :: l)) = list_not_gap (allocate r l).
Proof.
  intros l r b. unfold allocate. case r.
  - intros. rewrite H. apply lng_equal_minus in H. rewrite H. reflexivity.
  - unfold bl_first at 1. case b. intros. unfold list_not_gap at 1. fold list_not_gap.
    unfold block_form_list at 1. unfold badd, bsize. rewrite plus_n_m.
    apply lng_relate_minus_bfl in H. rewrite H. unfold bl_first. case l.
    + simpl. reflexivity.
    + intros. destruct b0. unfold list_not_gap at 2. unfold block_form_list at 1.
      unfold badd, bsize. rewrite plus_n_m. fold list_not_gap. unfold list_not_gap at 1.
      case (block_form_list (flag0, first0, size0) l0). fold list_not_gap.
      reflexivity. reflexivity. Qed.

(**allocate-list_not_zeroB *)
(*** ===========================================================*)
Lemma lnz_equal_minus : forall (b: Block)(l: blocklist),
  list_not_zeroB (b :: l) = true -> list_not_zeroB l = true.
Proof.
  intros. unfold list_not_zeroB in H. case (block_empty b) in H.
  - discriminate.
  - fold list_not_zeroB in H. assumption. Qed.

Lemma lnz_relate_allocate : forall (l: blocklist)(r: nat)(b: Block),
  list_not_zeroB (b :: l) = true ->
    list_not_zeroB (allocate r (b :: l)) = list_not_zeroB (allocate r l).
Proof.
  intros l r b. unfold allocate. case r.
  - intros. rewrite H. apply lnz_equal_minus in H. rewrite H. reflexivity.
  - unfold bl_first. case b. unfold list_not_zeroB at 2. fold list_not_zeroB.
    unfold block_empty. intros flag first size. case size.
    + intros. unfold list_not_zeroB in H. unfold block_empty in H. discriminate.
    + intros. case l.
      * simpl. reflexivity.
      * intros. destruct b0. unfold list_not_zeroB at 2. unfold block_empty at 1.
        fold list_not_zeroB. unfold list_not_zeroB. fold list_not_zeroB. reflexivity. Qed.

(**release*)
(*** ===========================================================*)

Lemma btf_eqblocklist : forall (b: Block)(l: blocklist),
  eqblocklist (b :: l) (bust_to_free b :: l) = true.
Proof.
  intros. unfold bust_to_free. case b. intros.
  unfold eqblocklist. unfold eqblock. rewrite eqb_refl. rewrite eqb_refl.
  apply eqblocklist_refl. Qed.

Lemma bl_release_equal : forall (l: blocklist)(b: Block),
  eqblocklist l (release b l) = true.
Proof.
  intros. induction l.
  - simpl. reflexivity.
  - unfold release. case (eqblock b0 b).
    + apply btf_eqblocklist.
    + unfold eqblocklist. rewrite eqblock_refl. fold eqblocklist. 
      fold release. assumption. Qed.

(*
Lemma bl_end_release_equal : forall (l: blocklist)(b: Block),
  block_from_zero (bl_end l) = block_from_zero (bl_end (release b l)).
Proof.
  intros. induction l.
  - simpl. unfold release, bl_end, block_from_zero; simpl. reflexivity.
  - unfold release; simpl.
    + reflexivity.
    + case b; simpl. intros. rewrite <- bl_end_add. reflexivity. Qed.
*)

(*
Lemma blf_release_equal : forall (l1 l2: blocklist),
  eqblocklist l1 l2 = true -> list_from_zero l1 = list_from_zero l2.
Proof.
  intros l1 l2. induction l1.
  - simpl. case l2. 
    + simpl. reflexivity.
    + intros. discriminate.
  - induction l2.
    + simpl. intros. discriminate.
    + 
*)

(*
Lemma lnp_minus_allocate: forall (b: Block)(l: blocklist)(r:nat),
  block_form_list b l = true -> list_not_gap l = true ->
    list_not_gap (allocate r (b :: l)) = list_not_gap (allocate r l).
Proof.
  intros. unfold allocate. case r.
  - apply lng_relate_bfl in H. 
    + rewrite H; rewrite H0; reflexivity.
    + assumption.
  - intros. 
*)




(*release*)
(*** ===========================================================*)
(*
Lemma release_equal : forall (l: blocklist), forall (b: Block),
  eqblocklist l (release b l) = true.
Proof.
  intros. 
  - simpl. induction l.
unfold release; simpl.
  - unfold release; simpl. case (eqblock b0 b); simpl.
    + simpl. rewrite eqblock_bust_to_free. rewrite eqblocklist_refl. reflexivity.
    + rewrite eqblock_refl. case (eqblock h bl); simpl.
*)




  