Require Import Program Setoid Bool.
Require Import Containers.Sets Containers.SetConstructs SetDecide.
Require SetAVLInstance.
Require Import SetoidList Equality.
Require Import Typex.Automata.Init.

Generalizable Variables A Σ Q.

Notation "(===)" := equiv (only parsing).

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
  | Left (q : Q) (H : q \In states_set) 
  | Right (q : Q) (H : q \In states_set).

  Fixpoint left_states (θ : formula) : set Q :=
    match θ with
      | Disj f g | Conj f g => union (left_states f) (left_states g)
      | Neg f => left_states f
      | Left q _ => {q}
      | _ => {}
    end.

  Fixpoint right_states (θ : formula) : set Q :=
    match θ with
      | Disj f g | Conj f g => union (left_states f) (left_states g)
      | Neg f => left_states f
      | Right q _ => {q}
      | _ => {}
    end.

  Fixpoint states_of (θ : formula) : set Q * set Q :=
    match θ with
      | Disj f g 
      | Conj f g => 
        let (leftf, rightf) := states_of f in
        let (leftg, rightg) := states_of g in
          (union leftf leftg, union rightf rightg)
      | Neg f => states_of f
      | Left q _ => ({q}%set, {})
      | Right q _ => ({}, {q})
      | _ => ({}, {})
    end.

  Lemma states_of_spec θ : forall l r,
                             states_of θ = (l, r) -> l [<=] states_set /\ r [<=] states_set.
  Proof. 
    induction θ; intros l r Heq; depelim Heq; try intuition fsetdec. 
    
    simpl in x. do 2 destruct states_of. specialize_eqs IHθ1. specialize_eqs IHθ2.
    depelim x. intuition fsetdec.
    
    simpl in x. do 2 destruct states_of. specialize_eqs IHθ1. specialize_eqs IHθ2.
    depelim x. intuition fsetdec.
    
    simpl in x. destruct states_of. specialize_eqs IHθ.
    depelim x. intuition fsetdec.
  Qed.

End Formulas.

Coercion Is_true : bool >-> Sortclass.

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
      trans_L_inh : not (is_empty trans_L);
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
      * order.
      * now (rewrite H1 in H; destruct H; order).

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
  Class ASTA Σ Q := 
    { auto_Σ :> Alphabet Σ;
      auto_Q :> States Q;
      auto_top_states : { s : set Q | s [<=] auto_Q } ;
      auto_transitions : Transitions }.
End Automaton.

Section Tree.
  Context `{A:Alphabet Σ}.
  
  (** Direction *)
  Definition direction := bool (* = 1 or 2 *).
  Delimit Scope direction_scope with dir.
  Notation "1" := false : direction_scope.
  Notation "2" := true : direction_scope.
  Open Scope direction_scope.
  Bind Scope direction_scope with direction.

  (** Nodes are cons lists: the begining of the list is the first move in the tree. *)
  Definition node := list direction.
  Definition empty_node : node := nil.
  Notation "'ε'" := empty_node : node_scope.
  Bind Scope node_scope with node.
  Open Scope node_scope.
  
  Infix "@" := (@app direction) (right associativity, at level 60) : node_scope.

  Definition dir_to_node (d : direction) : node := [d].
  Coercion dir_to_node : direction >-> node.
  
  Notation " n • d " := (n @ dir_to_node d) (at level 60).
  Notation " (• d ) " := (fun n => n @ dir_to_node d) (at level 40).
    
  (** Automatically inferred order on lists of booleans. *)
  Instance node_ot : OrderedType node | 0 := SOT_as_OT.
  Instance node_set_inst: @FSet node node_ot := _.
  Instance node_set_specs: FSetSpecs node_set_inst := _.
  Definition node_set := set node.

  Hint Unfold empty_node : asta.

  Lemma app_node_eps_l n : ε @ n === n.
  Proof. reflexivity. Qed.
  Lemma app_node_eps_r n : n @ ε === n.
  Proof. apply app_nil_r. Qed.
  Hint Rewrite app_node_eps_l app_node_eps_l : asta.

  Lemma app_node_assoc n m p : (n @ m) @ p === n @ m @ p.
  Proof. autounfold with asta; now rewrite app_assoc. Qed.
  Hint Rewrite app_node_assoc : asta.

  Lemma node_app_eq_l (l l' l'' : node) : (l @ l' === l @ l'' -> l' === l'').
  Proof. intros H. reduce in H. 
     now apply app_inv_head in H. 
  Qed.

  Lemma node_app_eq_r (l l' l'' : node) : (l' @ l === l'' @ l -> l' === l'').
  Proof. intros H. reduce in H; now apply app_inv_tail in H. Qed.

  Lemma node_app_eq_tail (l l' : node) : (l === l @ l' -> l' === ε).
  Proof. setoid_rewrite <- (app_node_eps_r l) at 1. intros; now apply node_app_eq_l in H. Qed.

  Lemma node_app_eq_head (l l' : node) : (l === l' @ l -> l' === ε).
  Proof. change l with (ε @ l) at 1. intros; now apply node_app_eq_r in H. Qed.

  Lemma empty_snoc_app π d n : ~ ε === (π • d) @ n.
  Proof. destruct π; intro; try discriminate. Qed.

  Lemma app_snoc n d π : (π • d) @ n === π @ [d] @ n.
  Proof. rewrite <- app_node_assoc. reflexivity. Qed.
  Hint Rewrite app_snoc : asta.

  Lemma node_app_eq_l_length (l0 l1 l2 l3 : node) : 
    l0 @ l1 === l2 @ l3 -> length l0 = length l2 -> l0 === l2 /\ l1 === l3.
  Proof. revert l0 l2 l3; induction l0; destruct l2; simpl; intros;
     autorewrite with list in H; try discriminate.

     now idtac.

     depelim H. specialize (IHl0 _ _ x). forward IHl0. intuition congruence.
     auto with arith.
  Qed.

  Lemma node_app_length π π' : length (π @ π') = length π + length π'.
  Proof. autorewrite with list; auto with arith. Qed.

  Lemma snoc_length π d : length (π • d) = length π + 1.
  Proof. apply node_app_length. Qed.

  Hint Rewrite node_app_length snoc_length : asta.

  Lemma node_app_nil (l l' : node) : (l @ l' === [] -> l === [] /\ l' === [])%list. 
  Proof. induction l; intros; simpl; auto. discriminate H. Qed.

  (** The trees we consider here *)
  Inductive binary_tree :=
  | tree_leaf | tree_node (l : Σ) (t1 t2 : binary_tree).

  
  Section Domain.
  
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

    Lemma dom_aux_node l t1 t2 π :
      dom_aux (tree_node l t1 t2) π = {π; dom_aux t1 (π • 1)} ++ dom_aux t2 (π • 2)%set.
    Proof. reflexivity. Qed.
    
    Hint Rewrite domain_leaf dom_aux_node : asta.

    Notation "d ∙ π" := (@cons direction d%dir π) (at level 0, only parsing) : node_scope.
    
    (** Characterisation as an inductive relation. *)
    Inductive Dom : binary_tree -> node -> Prop:= 
    | dom_leaf t : Dom t ε
    | dom_node_1 {l t1 t2 π} : Dom t1 π -> Dom (tree_node l t1 t2) (1 ∙ π)
    | dom_node_2 {l t1 t2 π} : Dom t2 π -> Dom (tree_node l t1 t2) (2 ∙ π).
    Hint Constructors Dom : asta.

    Ltac easy ::= auto with asta || order || easy_base.
    
    Instance Dom_proper : Proper ((===) ==> (===) ==> iff) Dom. 
    Proof with easy.
      assert (Proper (equiv ==> equiv ==> impl) Dom).
      reduce. 
      reduce in H. subst y. 
      reduce in H0. subst x0; auto.

      reduce.
      split. 
      apply H; auto.
      symmetry in H0, H1.
      apply H; auto.
    Qed.

    Lemma dom_aux_cur : forall t π, π \In dom_aux t π.
    Proof. destruct t; unfold dom_aux; fsetdec. Qed.  

    Lemma domain_ε t : ε \In domain t.
    Proof. unfold domain. apply dom_aux_cur. Qed.
    Hint Resolve dom_aux_cur domain_leaf domain_ε : asta.

    Instance: Proper ((===) ==> eq) (@length direction).
    Proof. reduce.
           induction H; auto.
    Qed.    

    Ltac simp := simpl in *; autorewrite with asta set_simpl in *.
    
    Lemma Dom_dom_aux t : forall n, Dom t n -> forall π, (π @ n) \In dom_aux t π.
    Proof with try easy. 
      intros. revert π. induction H; intros; auto with asta.
      now rewrite app_nil_r.

      simp. left; right. now rewrite app_comm_cons'. 
      simp; right. now rewrite app_comm_cons'.
    Qed.

    Lemma Dom_domain t : forall n, Dom t n -> n \In domain t.
    Proof.
      intros.
      generalize (Dom_dom_aux t n H ε).
      now autorewrite with asta.
    Qed.

    Lemma dom_aux_length t : forall π n, π \In dom_aux t n -> length n <= length π.
    Proof.
      induction t; simpl; intros; auto with arith; autorewrite with asta set_simpl in H.
      now rewrite H. 

      destruct H as [[H|H]|H].
      now rewrite H.
      specialize (IHt1 _ _ H); autorewrite with asta in IHt1. omega.
      specialize (IHt2 _ _ H); autorewrite with asta in IHt2. omega.
    Qed.

    Lemma dom_aux_inv {t} : forall {π π' n}, π @ n \In dom_aux t π' -> 
                                             length π = length π' -> π = π'.
    Proof.
      induction t; simpl; intros; autorewrite with asta set_simpl in H; simpl; auto; intros.
      rewrite <- (app_node_eps_r π') in H. apply node_app_eq_l_length in H; intuition eauto.
      
      destruct H as [[H|H]|H].
      rewrite <- (app_node_eps_r π') in H. now (apply node_app_eq_l_length in H; intuition).
      
      destruct n. apply dom_aux_length in H. 
      autorewrite with asta in H. simpl in H. assert False; omega.
      rewrite app_comm_cons' in H. 
      specialize (IHt1 _ _ _ H). autorewrite with asta in IHt1. simpl in IHt1.
      forward IHt1.  simpl in IHt1. apply node_app_eq_l_length in IHt1; intuition auto.
      auto with arith.

      destruct n. apply dom_aux_length in H. 
      autorewrite with asta in H. simpl in H. assert False; omega.
      rewrite app_comm_cons' in H. 
      specialize (IHt2 _ _ _ H). autorewrite with asta in IHt2. simpl in IHt2.
      forward IHt2.  simpl in IHt2. apply node_app_eq_l_length in IHt2; intuition auto.
      auto with arith.
    Qed.

    Lemma dom_aux_Dom : forall n π t, (π @ n) \In dom_aux t π -> Dom t n.
    Proof with try easy.
      induction n; simpl; intros. constructor.

      rewrite app_comm_cons' in H.
      destruct t; simpl in H; autorewrite with asta set_simpl in H.

      - apply node_app_eq_tail in H; discriminate.

      - destruct H as [[H|H]|H].
        * apply node_app_eq_tail in H; discriminate.
        * rewrite app_assoc in H. pose (Hi:=dom_aux_inv H). apply node_app_eq_l in Hi. 
          depelim Hi. constructor. eauto. simp. auto with arith.
        * rewrite app_assoc in H. pose (Hi:=dom_aux_inv H). apply node_app_eq_l in Hi. 
          depelim Hi. constructor. eauto. simp. auto with arith.
    Qed.

    Lemma domain_Dom t : forall π, π \In domain t -> Dom t π.
    Proof with try easy.
      intros. apply dom_aux_Dom with ε. fold (domain t). rewrite app_node_eps_l. apply H.
    Qed.

    Lemma domain_Dom_iff t : forall n, Dom t n <-> n \In domain t.
    Proof. split; auto using domain_Dom, Dom_domain. Qed.
  End Domain.
  
  Section Label.

    Inductive Label := 
    | hash | label (l : Σ).

    Notation "#" := hash.
    Coercion label : Σ >-> Label.

    Program
    Fixpoint label_of (t : binary_tree) (π : node | Dom t π) : Label :=
      match t with
        | tree_leaf => hash
        | tree_node λ l r => 
          match π with
            | [] => label λ
            | false :: π' => label_of l π'
            | true :: π' => label_of r π'
          end
      end.

    Next Obligation. 
      depelim H. auto.
    Defined.

    Next Obligation. 
      depelim H. auto.
    Defined.
  End Label.

End Tree.

(* I hate this but... *)
Delimit Scope node_scope with node.
Bind Scope node_scope with node.
Delimit Scope direction_scope with direction.
Bind Scope direction_scope with direction.

Notation "'ε'" := empty_node : node_scope.
Notation "1" := (false : direction) : direction_scope.
Notation "2" := (true : direction) : direction_scope.
Infix "@" := (@app direction) (right associativity, at level 60) : node_scope.
Notation " n • d " := (n @ dir_to_node d)%node (at level 60).
Notation " (• d ) " := (fun n => n @ dir_to_node d)%node (at level 40).

(* BUG *)
Arguments binary_tree.
Implicit Arguments binary_tree [].

Require Import SetConstructs.

Definition power_union {A} `{OrderedType A} (s : set (set A)) : set A :=
  fold (fun a acc => union a acc) s {}.

Section SetComprehensions.

  Context `{OrderedType A} {B : Type} `{OrderedType B}.

  Definition from_compr (a : set A) (P : A -> bool) (f : A -> B) : set B :=
    map f (filter P a).

  Definition split (s : set (set A * set B)) : set A * set B :=
    (power_union (map fst s), power_union (map snd s)).

  (* Variable s : set. *)
  (* Check [ x \from s | true ]. *)
  (* Check [ x \from s | x == x ]. *)
End SetComprehensions.

Notation "[ 'set' x 'in' s | p ] " := (filter (fun x => p) s) 
                                          (at level 0, x at level 99).

(* Notation "[ 'set' x 'from' s , q | p ] " := (from_compr s (fun x => p) (fun x => q)) (x ident, at level 0). *)

Section Evaluation.
  Context `{A: ASTA Σ Q}.
  
  Variable eval_trans : forall (Γ1 Γ2 : set Q) (π : node) (trans : Transitions), set Q.

  (*
1 function eval asta (A, t, ⇡, r) =
2 if t(⇡) = # then return ; else
3 let trans ={(q,L,⌧τ,π) \in L | q \in r /\ t(π) \in L}in
4 let ri = {q|#i q \in θ, ∀ θ \in trans} in
5 let Γ1 = eval asta (A,t,⇡π · 1,r1)
6 and Γ2 = eval asta (A,t,⇡π · 2,r2)
7 in return eval trans(Γ1, Γ2, π⇡, trans)
   *)

  Open Scope node_scope. Open Scope direction_scope.
(*
  Program
  Fixpoint eval (t : binary_tree Σ) (π : node) (r : set Q) : set Q :=
    match label_of t π with
      | hash => {}
      | label l =>
        let trans := 
            [set t in auto_transitions | (t.(trans_q) \in r) && (l \in t.(trans_L))] 
        in
        let '(r1, r2) := split (map (states_of ∘ trans_Φ) trans) in
        let Γ1 := eval t (π @ [1]) r1 in
        let Γ2 := eval t (π @ [2]) r2 in
          eval_trans Γ1 Γ2 π trans
    end.
*)
End Evaluation.