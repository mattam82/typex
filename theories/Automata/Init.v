Require Import Wellfounded Wf_nat.
Require Import Program SetoidList Equality.
Require Import Arith.
Require Import SetDecide Containers.OrderedType.

(** Fix the easy tactic to include auto and order *)

Ltac easy_base :=
  let rec use_hyp H :=
      (match type of H with
         | _ /\ _ => exact H || destruct_hyp H
         | _ => try (solve [ inversion H ])
       end)
  with do_intro := (let H := fresh in
                    intro H; use_hyp H)
  with destruct_hyp H := (case H; clear H; do_intro; do_intro) in
  let rec use_hyps :=
   (match goal with
    | H:_ /\ _ |- _ => exact H || (destruct_hyp H; use_hyps)
    | H:_ |- _ => solve [ inversion H ]
    | _ => idtac
    end) in
  let rec do_atom :=
   ((solve [ reflexivity | symmetry ; trivial ]) ||
      contradiction  || (split; do_atom))
  with do_ccl := (trivial with eq_true; repeat do_intro; do_atom) in
  (use_hyps; do_ccl) || fail "Cannot solve this goal".

Ltac easy ::= solve [ auto || order || easy_base ] || fail "Cannot solve this goal".

Ltac depelim id ::= 
  do_depelim ltac:(fun hyp => do_case hyp) id 
  || (reduce in id; do_depelim ltac:(fun hyp => do_case hyp) id).

Ltac forward H := 
  match type of H with
    | ?X -> _ => cut X; [let H' := fresh in intro H'; specialize (H H'); clear H'|]
  end.

Lemma list_length_ind {A} {P : list A -> Prop}
      (Psucc : forall l, (forall l', length l' < length l -> P l') -> P l) : forall l, P l.
Proof.
  apply induction_ltof1 with (f := @length A).
  apply Psucc.
Qed.

Section ListLastInd.
  Context {A : Type}.
  Context (P : list A -> Prop)
          (Pnil : P [])
          (Papp_end : forall l x, P l -> P (l ++ [x])%list).
      
  Fixpoint list_split_last (l : list A) (opt : A) : list A * A :=
    match l with
      | [] => ([], opt)
      | a :: [] => ([opt], a)
      | a :: b :: l => 
          let (r, x) := list_split_last l b in
            (opt :: a :: r, x)
    end.

  Lemma list_split_last_spec l :
    forall opt l' a', list_split_last l opt = (l', a') -> opt :: l = (l' ++ [a'])%list.
  Proof. revert l.
    refine (list_length_ind _). intros.
    destruct l; depelim H0.
    reflexivity.

    simpl in x.
    destruct l. depelim x.
    reflexivity.

    case_eq (list_split_last l a0); intros l'' a'' Heq.
    rewrite Heq in x.
    depelim x.
    simpl. repeat f_equal.
    apply (H l). simpl. auto.
    auto.
  Qed.    
  
  Program 
  Fixpoint list_elim_last (l : list A) {measure (length l)} : P l :=
    match l with
      | [] => Pnil
      | a :: [] => Papp_end [] a Pnil
      | a :: l => 
          let '(l', b) := list_split_last l a in
            Papp_end l' b (list_elim_last l')
    end.
  
  Next Obligation.
  Proof.
    symmetry in Heq_anonymous. apply list_split_last_spec in Heq_anonymous.
    destruct l'; simpl; auto. auto with arith.
    simpl in Heq_anonymous. inversion Heq_anonymous; subst.
    rewrite app_length. simpl; rewrite NPeano.Nat.add_1_r. auto with datatypes arith.
  Qed.

  Next Obligation.
  Proof.
    symmetry in Heq_anonymous. apply list_split_last_spec in Heq_anonymous. auto.
  Qed.

End ListLastInd.

Lemma app_comm_cons' : forall A (x y:list A) (a:A), x ++ a :: y = (x ++ [a]) ++ y.
Proof. induction x; simpl; intros; auto. now rewrite IHx. Qed.
       