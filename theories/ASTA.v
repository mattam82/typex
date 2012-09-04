Require Import Program EquivDec Setoid.
Require Import Containers.Sets.
Require SetAVLInstance.
Generalizable Variables A Σ Q.
Check set nat.
Check {1; {}}.

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

Ltac easy ::= auto || order || easy_base.

(* (** Overloaded equivalence operator using definitional type classes. *) *)
(* Class Equiv (A : Type) := equiv : relation A. *)
(* Infix "==" := equiv. *)
(* Notation "(==)" := equiv. *)

(** An alphabet is a finite set with a decidable equivalence relation. *)

Class Alphabet (A : Type) := 
  { alpha_ordered :> OrderedType A;
    alpha_set : set A }.

Coercion alpha_set : Alphabet >-> set.

(** States form an ordered type so we can build finite sets of states, compare them etc..
    [OrderedType] is a typeclass as well.
 *)

Class States (A : Type) :=
  { states_ordered :> OrderedType A;
    states_set : set A }.

Coercion states_set : States >-> set.

(** Boolean formulas *)
Section Formulas.

  Context `{S : States Q}.

  Inductive formula :=
  | Top | Bottom
  | Disj (f g : formula)
  | Conj (f g : formula)
  | Neg (f : formula)
  | Left (f : formula) (q : Q) (H : q \In states_set) 
  | Right (f : formula) (q : Q) (H : q \In states_set).

End Formulas.
(** Transitions *)

Section Transitions.
  Context `{A:Alphabet Σ, S:States Q}.

  (** Is it a selecting transition or not? *)
  Inductive selecting : Set := select | traverse.

  (** One transition. *)
  Record Transition := 
    { trans_q : Q;
      trans_L : set Σ;
      trans_L_incl : trans_L [<=] alpha_set;
      trans_select : selecting;
      trans_Φ : formula }. 

  (** Set of transitions. *)
  Require Import Generate.

  Definition eq_transition t t' :=
    t.(trans_q) === t'.(trans_q) /\
    t.(trans_L) === t'.(trans_L).
(* Question ? *)
    (* t.(trans_select) === t'.(trans_select) /\ *)
    (* t.(trans_Φ) === t'.(trans_Φ). *)

  Definition lt_transition t t' :=
    t.(trans_q) <<< t'.(trans_q) \/
     (t.(trans_q) === t'.(trans_q) /\ t.(trans_L) <<< t'.(trans_L)).

  Definition cmp_transition t t' :=
    match t.(trans_q) =?= t'.(trans_q) with
    | Eq => t.(trans_L) =?= t'.(trans_L)
    | x => x
    end.

  Instance eq_equiv : Equivalence eq_transition.
  Proof.
    unfold eq_transition. split; red; intros.
    split; reflexivity.
    intuition symmetry; auto.
    intuition (etransitivity; eauto).
  Qed.
  

  Instance trans_ord : OrderedType Transition := 
    { _eq := eq_transition; _lt := lt_transition;
      _cmp := cmp_transition }.
  Proof.
    unfold lt_transition.
    constructor. red; intros.

    - intuition (try etransitivity; eauto).
      now rewrite H0 in H1. 
      now rewrite <- H in H1.

    - intros; red; intros.
      destruct H0.
      destruct H.
      * now rewrite H0 in H.
      * now rewrite H1 in H.
      destruct H; order.

    - intros. unfold cmp_transition; simpl.
      case_eq (compare (trans_q x) (trans_q y)); intros; try constructor.
      case_eq (compare (trans_L x) (trans_L y)); intros; try constructor.
      apply compare_2 in H. apply compare_2 in H0. 
      now red. 

      apply compare_2 in H; apply compare_1 in H0.
      now red. 

      apply compare_2 in H; apply compare_3 in H0.
      now red. 

      apply compare_1 in H. 
      now red. 

      apply compare_3 in H. 
      now red. 
  Qed.

  Definition Transitions := set Transition.

End Transitions.

Section Automaton.
  Record ASTA Σ Q := 
    { auto_Σ :> Alphabet Σ;
      auto_Q :> States Q;
      auto_top_states : { s : set Q | s [<=] auto_Q } ;
      auto_transitions : Transitions }.
End Automaton.

Section Tree.
  Context `{A:Alphabet Σ}.

  Inductive binary_tree :=
  | tree_leaf | tree_node (l : Σ) (t1 t2 : binary_tree).
  
  (** Direction *)
  Definition direction := bool (* = 1 or 2 *).
  Delimit Scope direction_scope with dir.
  Notation "1" := false : direction_scope.
  Notation "2" := true : direction_scope.

  Definition node := list direction.
  Definition empty_node : node := nil.
  Definition snoc_node (n : node) (d : direction) : node :=
    d :: n.
  
  Notation " n • l " := (snoc_node n l%dir) (at level 60).
  Notation "'ε'" := empty_node.

  (** Automatically inferred order on lists of booleans. *)
  Instance direction_ot : OrderedType node := _.
  Instance node_set_inst: @FSet node _ := _.
  Instance node_set_specs: FSetSpecs node_set_inst := _.
  Definition node_set := set node.

  (** Computing the domain of a tree. *)
  Fixpoint dom_aux (t : binary_tree) cur : node_set :=
    match t with
      | tree_leaf => {cur}
      | tree_node l t1 t2 => {cur; dom_aux t1 (cur • 1)} ++
                                 dom_aux t2 (cur • 2)
    end.

  Definition domain t := dom_aux t ε.

  (** Characterisation as an inductive relation. *)
  Inductive Dom : binary_tree -> node -> Prop:= 
  | dom_leaf t : Dom t ε
  | dom_node l t1 t2 π : Dom t1 (π • 1) -> Dom t2 (π • 2) -> Dom (tree_node l t1 t2) π.

  (* BUG with autorewrite and typeclasses! Damnit *)
  Hint Rewrite @singleton_iff using typeclasses eauto : myset.
  Require Import SetDecide.

  Lemma domain_leaf : forall t, ε \In domain t.
  Proof. destruct t; unfold domain. unfold dom_aux. fsetdec. FSetDecideAuxiliary.discard_nonFSet. autorewrite with set_simpl. reflexivity. typeclasses eauto. fsetdec.
  Lemma domain_Dom t : forall n, Dom t n <-> n \In domain t.
  Proof. split; intros.
    - induction H.
      simpl.

End Tree.
Section Evaluation.
  Context `{A: ASTA Σ Q}.

  

  