Require Import Program Setoid.
Require Import Containers.Sets.
Require SetAVLInstance.
Generalizable Variables A Σ Q.

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

Section ListLastInd.
  Context {A} (P : list A -> Type)
          (Pnil : P [])
          (Papp_end : forall l, P l -> forall x, P (l ++ [x])%list).

  Fixpoint list_split_last (l : list A) (opt : A) : list A * A :=
    match l with
      | [] => ([], opt)
      | a :: [] => ([opt], a)
      | a :: b :: l => 
          let (r, x) := list_split_last l b in
            (opt :: a :: r, x)
    end.

  Lemma list_split_last_spec l : l <> [] -> 
    forall opt l' a', list_split_last l opt = (l', a') -> opt :: l = (l' ++ [a'])%list.
  Proof.
    induction l; simpl; intros; auto.

    now elim H.

    destruct l. depelim H0.
    reflexivity.

    assert(Hd:a0 :: l <> []) by (intro; discriminate).
    revert H0; case_eq (list_split_last l a0). intros.
    depelim H1.
    simpl. repeat f_equal.
    specialize (IHl Hd).
    specialize (IHl opt (opt :: l0) a').
    simpl in IHl.
    destruct l.
    simpl in H0. depelim H0. reflexivity.
    
    
    
  Program Fixpoint list_elim_last 
                     (l : list A) {measure (length l)} : P l :=
    match l with
      | [] => Pnil
      | a :: [] => Papp_end [] Pnil a
      | a :: l => 
          let (l', b) := split_last l in
            Papp_end l (a :: l') b
    end.

Section Tree.
  Context `{A:Alphabet Σ}.

  Inductive binary_tree :=
  | tree_leaf | tree_node (l : Σ) (t1 t2 : binary_tree).
  
  (** Direction *)
  Definition direction := bool (* = 1 or 2 *).
  Delimit Scope direction_scope with dir.
  Definition left : direction := false.
  Definition right : direction := true.
  Notation "1" := left : direction_scope.
  Notation "2" := right : direction_scope.
  Open Scope direction_scope.

  (** Nodes are snoc lists: addition at the end of the list. *)
  Definition node := list direction.
  Definition empty_node : node := nil.
  Definition snoc_node (n : node) (d : direction) : node :=
    d :: n.

  Definition app_node (n n' : node) : node := (n' ++ n)%list.
  
  Notation " n • l " := (snoc_node n l%dir) (at level 60).
  Notation " (• l ) " := (fun n => snoc_node n l%dir) (at level 40).

  Notation "'ε'" := empty_node.
  Infix "@" := app_node (at level 50). 

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

  Lemma domain_leaf : domain tree_leaf = {ε}%set.
  Proof. reflexivity. Qed.
  Require Import Containers.SetConstructs.
  Lemma dom_aux_node l t1 t2 π : dom_aux (tree_node l t1 t2) π = {π; dom_aux t1 (π • 1)} ++ dom_aux t2 (π • 2)%set.
  Proof. reflexivity. Qed.
  
  Hint Rewrite domain_leaf dom_aux_node : asta.

  Definition dir_to_node (d : direction) : node := [d].
  Coercion dir_to_node : direction >-> node.
  
  (** Characterisation as an inductive relation. *)
  Inductive Dom : binary_tree -> node -> Prop:= 
  | dom_leaf t : Dom t ε
  | dom_node_1 {l t1 t2 π} : Dom t1 π -> Dom (tree_node l t1 t2) (1 @ π)
  | dom_node_2 {l t1 t2 π} : Dom t2 π -> Dom (tree_node l t1 t2) (2 @ π).
  Hint Constructors Dom : asta.

  Ltac easy ::= auto with asta || order || easy_base.

  Notation "(===)" := equiv (only parsing).

  Require Import SetoidList.

  Instance snoc_Proper : Proper ((===) ==> (===) ==> (===)) snoc_node.
  Proof. reduce.
    repeat reduce in H.
    repeat reduce in H0. subst x0.
    constructor; auto.
  Qed.

  Instance app_Proper : Proper ((===) ==> (===) ==> (===)) app_node.
  Proof. reduce.
    repeat reduce in H; repeat reduce in H0. 
    induction H0. simpl. auto.
    simpl.
    constructor; auto.
  Qed.
    
  Instance Dom_proper : Proper ((===) ==> (===) ==> iff) Dom. 
  Proof with easy.
    assert (Proper (equiv ==> equiv ==> impl) Dom).
    reduce. 
    reduce in H. subst y. 
    revert y0 H0; induction H1; intros. 
    now inversion H0.

    destruct y0.
    constructor.
    
    destruct d; try constructor.
    

    repeat red in H0. depelim H0. 

    repeat red in H0. 
    unfold _eq in *. unfold SOT_as_OT in H0.
    depelim H0. constructor. auto.

    repeat red in H0. 
    unfold _eq in *. unfold SOT_as_OT in H0.
    depelim H0. rewrite x. constructor. auto.

    reduce.
    split. 
    apply H; auto.
    symmetry in H0, H1.
    apply H; auto.
  Qed.

  (* BUG with autorewrite and typeclasses! Damnit *)
  Hint Rewrite @singleton_iff using typeclasses eauto : myset.
  Require Import SetDecide.

  Lemma dom_aux_cur : forall t π, π \In dom_aux t π.
  Proof. destruct t; unfold dom_aux; fsetdec. Qed.  

  Lemma domain_ε t : ε \In domain t.
  Proof. unfold domain. apply dom_aux_cur. Qed.
  Hint Resolve dom_aux_cur domain_leaf domain_ε : asta.

  Require Import Equality.

  Lemma list_app_nil (l l' : node) : (l @ l' = [] -> l = [] /\ l' = [])%list. 
  Proof. induction l'; intros; simpl; auto.
    discriminate H. 
  Qed.

  Lemma app_inv_head:
   forall l l1 l2 : node, (l ++ l1 === l ++ l2 -> l1 === l2)%list.
  Proof.
    induction l; simpl; auto. intros. red in H; depelim H; auto.
  Qed.

  Instance: Proper ((===) ==> eq) (@length direction).
  Proof. reduce.
    induction H; auto.
    simpl; now rewrite IHlist_eq.
  Qed.    

  Lemma app_inv_tail:
    forall l l1 l2 : node, (l1 ++ l === l2 ++ l -> l1 === l2)%list.
  Proof.
    intros l l1 l2; revert l1 l2 l.
    induction l1 as [ | x1 l1]; destruct l2 as [ | x2 l2];
     simpl; auto; intros l H.
    absurd (length (x2 :: l2 ++ l)%list <= length l).
    simpl; rewrite app_length; auto with arith. 
    rewrite <- H; auto with arith.
    absurd (length (x1 :: l1 ++ l)%list <= length l).
    simpl; rewrite app_length; auto with arith.
    rewrite H; auto with arith.
    red in H; depelim H; intros. pose (IHl1 _ _ H0). now apply snoc_Proper.
  Qed.

  Lemma list_app_eq (l l' : node) : (l === l @ l' -> l' === ε).
  Proof. change l with (l @ ε) at 1.
    intros. unfold app_node in H. now apply app_inv_tail in H.
  Qed.

  Lemma list_app_eq' (l l' : node) : (l === l' @ l -> l' === ε).
  Proof. setoid_replace l with (ε @ l) at 1.
    intros. unfold app_node in H. now apply app_inv_head in H.
    unfold app_node. now rewrite app_nil_r.
  Qed.

  Ltac simp := autorewrite with set_simpl in *.
 
  Lemma Dom_dom_aux t : forall n, Dom t n -> forall π, (π @ n) \In dom_aux t π.
  Proof with try easy. intros. induction H. 
    now simpl. 
    
    simpl.
    autorewrite with set_simpl. left; right.
    
    Lemma dom_aux_snoc t π : dom_aux t π === map (app_node π) (dom_aux t ε).
    Proof.
      induction t; simpl; try easy; intro; setoid_rewrite map_iff; try typeclasses eauto.
      split; intros. exists ε; split; fsetdec.
      destruct H as [a' [aIn aeq]].
      rewrite aeq. autorewrite with set_simpl in aIn. rewrite <- aIn in aeq |- *.
      simpl; fsetdec.

      split; intros. autorewrite with set_simpl in H. 
      destruct H as [[H|H]|H].
      exists ε. fsetdec.

      exists [1%dir]. simp. split. left. right. easy. 
      

      typeclasses eauto.

      intro elt. setoid_Rewrite
      
      red. red.
      rewrite fold_1. rewrite elements_singleton.
      unfold elements; simpl.
 autorewrite with set_simpl.

    Lemma dom_aux_extend π n t : π @ n \In dom_aux t π -> forall d, (π • d) @ n \In dom_aux t (π • d).
    Proof with easy.
      revert π n; induction t; simpl; intros.
      autorewrite with set_simpl in H.
      apply list_app_eq in H. now rewrite H; fsetdec.

      autorewrite with set_simpl in H.
      destruct H. destruct H.
      apply list_app_eq in H. now rewrite H; fsetdec.
      autorewrite with set_simpl.
      left. right.
      
      

    symmetry in x; apply list_app_nil in x. destruct x as [-> ->]. apply domain_ε.
    
    simpl. 
    specialize (IHDom1 (π • 1) n eq_refl).
    specialize (IHDom2 (π • 2) n eq_refl).
    fsetdec.
  Qed.

  Lemma Dom_domain t : forall n, Dom t n -> n \In domain t.
  Proof with try easy. intros; now apply Dom_dom_aux. Qed.

  Lemma dom_aux_Dom t : forall n π, (π @ n) \In dom_aux t n -> Dom t π.
  Proof with try easy. 
    induction t; intros. simpl in H.
    autorewrite with asta set_simpl in H. apply list_app_eq' in H.
    now rewrite H.

    simpl in H.
    constructor. eapply IHt1. [apply IHt1 |apply IHt2]; auto.
    unfold domain in H |- *; rewrite dom_aux_node in H.

  Qed.

  Lemma dom_aux_Dom t : forall π, π \In domain t -> Dom t π.
  Proof with try easy. 
    induction t; intros.
    autorewrite with asta set_simpl in H. now rewrite <- H.

    constructor; [apply IHt1|apply IHt2]; auto.
    unfold domain in H |- *; rewrite dom_aux_node in H.

  Qed.
      

  Lemma domain_Dom t : forall n, Dom t n <-> n \In domain t.
  Proof with try easy. split; intros.
    - induction H... 
      unfold domain; rewrite dom_aux_node.
     


End Tree.
Section Evaluation.
  Context `{A: ASTA Σ Q}.

  

  