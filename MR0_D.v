Require Import Bool.

(**some compute*)
(*** ===========================================================*)
(*two number equal*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

(**Block*)
(*** ===========================================================*)

Inductive FlagB : Type :=
  | busy
  | free.

Definition flagSame (st1 st2 : FlagB) : bool :=
  match st1 with
  | busy => match st2 with
            | busy => true
            | free => false
            end
  | free => match st2 with
            | busy => false
            | free => true
            end
  end.

Inductive Block : Type :=
  | block (flag: FlagB)(first size: nat).

Notation "( f , x , y )" := (block f x y).

(*Block status*)
Definition bflag (b : Block) : FlagB :=
  match b with
  | (f, a, s) => f
  end.

(*Block address*)
Definition badd (b : Block) : nat :=
  match b with
  | (f, a, d) => a
  end.

(*Block size*)
Definition bsize (b : Block) : nat :=
  match b with
  | (f, a, s) => s
  end.

Definition block_from_zero (b : Block) : bool :=
  match b with
  | (_, O, _) => true
  | (_, _, _) => false
  end.

Definition block_empty (b : Block) : bool :=
  match b with
  | (_, _, O) => true
  | (_, _, _) => false
  end.

Definition eqblock (b1 b2 : Block) : bool :=
  match b1 with (_, a1, s1) => match b2 with (_, a2, s2) => 
  match a1 =? a2 with
  | true => match s1 =? s2 with
            | true => true
            | false => false
            end
  | false => false
  end
  end
  end.

Definition eqblock_state (b1 b2 : Block) : bool :=
  match b1 with (st1, a1, s1) => match b2 with (st2, a2, s2) => 
  match (flagSame st1 st2) with
  | true => match a1 =? a2 with
          | true => match s1 =? s2 with
                    | true => true
                    | false => false
                    end
          | false => false
          end
  | false => false
  end
  end
  end.

Definition eqblock_busy (b1 b2 : Block) : bool :=
  match b1 with (st1, a1, s1) => match b2 with (st2, a2, s2) =>
  match st1 with
  | busy => match (flagSame st1 st2) with
            | true => match a1 =? a2 with
                    | true => match s1 =? s2 with
                              | true => true
                              | false => false
                              end
                    | false => false
                    end
            | false => false
            end
  | free => false
  end
  end
  end.

(**BlockList definition*)
(*** ===========================================================*)
Inductive blocklist : Set :=
  | block_nil
  | block_cons (b : Block) (l : blocklist).

Notation "b :: l" := (block_cons b l).
Notation "[ ]" := block_nil.
Notation "[ x ; .. ; y ]" := (block_cons x .. (block_cons y block_nil) ..).

Fixpoint eqblocklist (l1 l2:blocklist) : bool :=
  match l1 with
  | block_nil => match l2 with 
           | block_nil => true
           | h2 :: t2 => false
           end
  | h1 :: t1 => match l2 with
                | block_nil => false
                | h2 :: t2 => match (eqblock h1 h2) with 
                              | true => eqblocklist t1 t2
                              | false => false
                              end
                end
  end.

Definition bl_first (l : blocklist): Block :=
  match l with
  | block_nil => (free, O, O)
  | h :: t => h
  end.

Eval compute in bl_first [(free, 1, 45);(busy, 6, 15)].

Fixpoint appbl (l1 l2 : blocklist) : blocklist :=
  match l1 with
  | block_nil    => l2
  | h :: t => h :: (appbl t l2)
  end.

Notation "x ++ y" := (appbl x y).

Fixpoint rev (l : blocklist) : blocklist :=
  match l with
  | block_nil    => block_nil
  | h :: t => rev t ++ [h]
  end.

Definition bl_end (l : blocklist): Block :=
  match rev l with
  | block_nil => (free, O, O)
  | h :: t => h
  end.

Eval compute in bl_end [(free, 1, 45);(busy, 6, 15)].

Definition bl_not_empty (l : blocklist): bool :=
  match bl_end l with
  | (_, O, O) => false
  | (_, _, _) => true
  end.

Definition block_form_list (b: Block)(l: blocklist): bool :=
  match l with
  | block_nil => true
  | h :: t => if (badd b) =? (badd h) + (bsize h) then true else false
  end.

Fixpoint busy_block_in_list (b : Block) (l : blocklist) : bool :=
  match l with
  | block_nil => false
  | h :: t => if (eqblock_busy h b) then true
                                    else busy_block_in_list b t
  end.

(**function*)
(*** ===========================================================*)

(*operation allocate*)
Definition allocate (r : nat) (l : blocklist) : blocklist :=
  match r with
  | O => l
  | _ => match bl_first l with
         | (_, a, d) => (busy, a+d, r) :: l
         end
  end.

Eval compute in allocate 0 ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]).

Eval compute in allocate 5 ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]).

Definition bust_to_free (b : Block) : Block :=
  match b with
  | (_, a, s) => (free, a, s)
  end.

(*operation free*)
Fixpoint release (b : Block) (l : blocklist) : blocklist :=
  match l with
  | block_nil => block_nil
  | h :: t => if (eqblock h b) then (bust_to_free h) :: t
                               else h :: (release b t)
  end.

Eval compute in release (busy, 59, 20) ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]).

Hint Resolve allocate bust_to_free release : memorymanage.

(**character*)
(*** ===========================================================*)

(*1.memory address is nature from 0*)
Definition list_from_zero (l : blocklist) : bool :=
  match l with
  | block_nil => true
  | h :: t => block_from_zero (bl_end l)
  end.

Eval compute in list_from_zero ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]).

(*2.blocklist tail address less memory size*)
Definition list_tail_less_memory_size (l : blocklist) (mz : nat) : bool :=
  match l with
  | block_nil => true
  | h :: t => if (badd(h) + bsize(h)) <=? mz then true
                                          else false
  end.

Eval compute in list_tail_less_memory_size ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]) 87.

(*3.between Blocks have no gap; memory block is continue*)
Fixpoint list_not_gap (l : blocklist) : bool :=
  match l with
  | block_nil => true
  | h :: t => match (block_form_list h t) with
              | true => list_not_gap t
              | false => false
              end
  end.

Eval compute in list_not_gap ((busy, 59, 20) :: [(free, 14, 45);(busy, 0, 14)]).

(*4.no zero Block*)
Fixpoint list_not_zeroB (l : blocklist) : bool :=
  match l with
  | block_nil => true
  | h :: t => match (block_empty h) with
              | true => false
              | false => list_not_zeroB t
              end
  end.

Hint Resolve list_from_zero list_not_gap list_not_zeroB : memorymanage.

Let H1 := [(busy, 68, 10);(busy, 48, 20);(busy, 37, 11);(busy, 19, 18);(busy, 6, 13);(busy, 0, 6)].
Eval compute in list_from_zero H1.
Eval compute in list_tail_less_memory_size H1 80.
Eval compute in list_not_gap H1.
Eval compute in list_not_zeroB H1.





