Require Import Program Setoid Bool.
Require Import Containers.Sets Containers.SetConstructs SetDecide.
Require SetAVLInstance.
Require Import SetoidList Equality.
Require Import Typex.Init.

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
  | Left (f : formula) (q : Q) (H : q \In states_set) 
  | Right (f : formula) (q : Q) (H : q \In states_set).

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
  Record ASTA Σ Q := 
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
  Infix "@" := app_node (right associativity, at level 60).
    
  (** Automatically inferred order on lists of booleans. *)
  Instance node_ot : OrderedType node | 0 := SOT_as_OT.
  Instance node_set_inst: @FSet node node_ot := _.
  Instance node_set_specs: FSetSpecs node_set_inst := _.
  Definition node_set := set node.

  Hint Unfold app_node empty_node snoc_node : asta.

  Lemma app_node_eps_l n : ε @ n === n.
  Proof. autounfold with asta; now rewrite app_nil_r. Qed.
  Lemma app_node_eps_r n : n @ ε === n.
  Proof. reflexivity. Qed.
  Hint Rewrite app_node_eps_l app_node_eps_l : asta.

  Lemma app_node_assoc n m p : (n @ m) @ p === n @ m @ p.
  Proof. autounfold with asta; now rewrite app_assoc. Qed.
  Hint Rewrite app_node_assoc : asta.

  Lemma node_app_eq_l (l l' l'' : node) : (l @ l' === l @ l'' -> l' === l'').
  Proof. intros H. unfold app_node, empty_node in H. reduce in H. 
     now apply app_inv_tail in H. 
  Qed.

  Lemma node_app_eq_r (l l' l'' : node) : (l' @ l === l'' @ l -> l' === l'').
  Proof. intros H. unfold app_node, empty_node in H. reduce in H. 
     now apply app_inv_head in H. 
  Qed.

  Lemma node_app_eq_tail (l l' : node) : (l === l @ l' -> l' === ε).
  Proof. change l with (l @ ε) at 1. intros; now apply node_app_eq_l in H. Qed.

  Lemma node_app_eq_head (l l' : node) : (l === l' @ l -> l' === ε).
  Proof. setoid_rewrite <- (app_node_eps_l l) at 1. intros; now apply node_app_eq_r in H. Qed.

  Lemma snoc_app_node π d : π • d === π @ [d].
  Proof. reflexivity. Qed.

  Lemma empty_snoc_app π d n : ~ ε === (π • d) @ n.
  Proof. destruct n; intro; discriminate. Qed.

  Lemma app_snoc n d π : (π • d) @ n === π @ [d] @ n.
  Proof. rewrite <- app_node_assoc. reflexivity. Qed.
  Hint Rewrite app_snoc : asta.

  Lemma node_app_eq_l_length (l0 l1 l2 l3 : node) : 
    l0 @ l1 === l2 @ l3 -> length l0 = length l2 -> l0 === l2 /\ l1 === l3.
  Proof. revert l0 l2 l3; induction l1; destruct l3; simpl; intros. 
     now idtac.

     rewrite H in H0.
     simpl in H0; unfold app_node in H0; autorewrite with list in H0.
     assert False; omega.
     rewrite <- H in H0.
     simpl in H0; unfold app_node in H0; autorewrite with list in H0.
     assert False; omega.

     depelim H. destruct (IHl1 _ _ _ x H0). now rewrite H, H1.
  Qed.

  Lemma node_app_length π π' : length (π @ π') = length π + length π'.
  Proof. unfold app_node; autorewrite with list; auto with arith. Qed.

  Lemma snoc_length π d : length (π • d) = length π + 1.
  Proof. unfold snoc_node; simpl; autorewrite with list; omega. Qed.

  Hint Rewrite node_app_length snoc_length : asta.

  Lemma node_app_nil (l l' : node) : (l @ l' === [] -> l === [] /\ l' === [])%list. 
  Proof. induction l'; intros; simpl; auto. discriminate H. Qed.

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

    Definition dir_to_node (d : direction) : node := [d].
    Coercion dir_to_node : direction >-> node.
    
    (** Characterisation as an inductive relation. *)
    Inductive Dom : binary_tree -> node -> Prop:= 
    | dom_leaf t : Dom t ε
    | dom_node_1 {l t1 t2 π} : Dom t1 π -> Dom (tree_node l t1 t2) (1 @ π)
    | dom_node_2 {l t1 t2 π} : Dom t2 π -> Dom (tree_node l t1 t2) (2 @ π).
    Hint Constructors Dom : asta.

    Ltac easy ::= auto with asta || order || easy_base.

    Instance snoc_Proper : Proper ((===) ==> (===) ==> (===)) snoc_node.
    Proof. reduce.
           repeat reduce in H.
           repeat reduce in H0. subst. reflexivity.
    Qed.

    Instance app_Proper : Proper ((===) ==> (===) ==> (===)) app_node.
    Proof. reduce.
           repeat reduce in H; repeat reduce in H0. subst; auto.
    Qed.
    
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
    Proof with try easy. intros. revert π. induction H; intros.
                         now simpl. 
                         
                         simp. left; right. rewrite <- app_node_assoc.
                         apply IHDom.

                         simp; 
                           autorewrite with set_simpl. right.
                         unfold app_node. rewrite app_assoc_reverse.
                         apply IHDom.
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

    Lemma dom_aux_inv t : forall π π' n, π @ n \In dom_aux t π' -> 
                                         length π = length π' -> π = π'.
    Proof.
      induction t; simpl; intros; autorewrite with asta set_simpl in H; simpl; auto; intros.
      rewrite <- app_node_eps_r in H. apply node_app_eq_l_length in H; intuition eauto.
      
      destruct H as [[H|H]|H].
      rewrite <- app_node_eps_r in H. now (apply node_app_eq_l_length in H; intuition).
      
      destruct n using list_elim_last. apply dom_aux_length in H. 
      autorewrite with asta in H. simpl in H. assert False; omega.
      fold ([x] @ l0) in *. rewrite <- app_node_assoc in H.
      specialize (IHt1 _ _ _ H). autorewrite with asta in IHt1. simpl in IHt1.
      forward IHt1. now depelim IHt1. auto with arith.
      
      destruct n using list_elim_last. apply dom_aux_length in H.
      autorewrite with asta in H. simpl in H. assert False; omega.
      fold ([x] @ l0) in *. rewrite <- app_node_assoc in H.
      specialize (IHt2 _ _ _ H). autorewrite with asta in IHt2. simpl in IHt2.
      forward IHt2. now depelim IHt2. auto with arith.
    Qed.

    Lemma dom_aux_Dom : forall n π t, (π @ n) \In dom_aux t π -> Dom t n.
    Proof with try easy. 
      refine (list_elim_last _ _ _); intros.
      constructor. 

      destruct t.
      simpl in H0.
      autorewrite with asta set_simpl in H0.
      apply node_app_eq_tail in H0.
      destruct l; simpl in H0; discriminate.

      unfold app_node, snoc_node in *. 
      simpl in H0.
      autorewrite with asta set_simpl in H0.
      destruct H0 as [[He|Ht]|Hf].
      apply node_app_eq_tail in He.
      elimtype False. destruct l; simpl in *; discriminate.
      
      rewrite <- app_assoc in Ht.
      destruct x. simpl in Ht.

      apply dom_aux_inv in Ht. discriminate.
      reflexivity.
      constructor; eapply H. apply Ht.

      destruct x; simpl in Hf. 
      rewrite <- app_assoc in Hf.
      constructor; eapply H. apply Hf.
      rewrite <- app_assoc in Hf.
      apply dom_aux_inv in Hf. discriminate.
      reflexivity.
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
      fold (snoc_node π' false) in H.
    (* Fixpoint label_of (t : binary_tree) (π : node) : Label := *)
    (*   match t with *)
    (*     | tree_leaf => hash *)
    (*     | tree_node λ l r =>  *)
    (*       match π with *)
    (*         | [] => label λ *)
    (*         | false :: π' => label_of l π' *)
    (*         | true :: π' => label_of r π' *)
    (*       end *)
    (*   end. *)

    Lemma label_dom t n : Dom t n -> label_of t n 
    

End Tree.
Section Evaluation.
  Context `{A: ASTA Σ Q}.

  Fixpoint eval (t : binary_tree) (π : node) (r : set Q) : set Q :=
    match t with
      | tree_leaf => {}
      | tree_node λ l r => 
 