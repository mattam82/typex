(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import setOrder.
Require Export XPath.
Require Import xnodes.
Require Import XPathInduction.
(* Require XPathBasicProp.*)
Require Import Mapping.
Require Import graphInt.
Require Export nat_basics.
Require Import XPequiv.

Require Import XPathGrammar.

(* ========================================================================================*)
(* This part defines all axioms of the theory in two mutually inductive definitions        *)
(*	this allows usefull inversions (see Inversion tactic)                              *)
(* ========================================================================================*)
 
Inductive Qualif : XPath -> Prop :=
    is_qualif : forall (p : XPath) (q : XQualif), Qualif (qualif p q).



Inductive Ple : XPath -> XPath -> Prop :=
 
  (* basics *)
  | p_void : forall p : XPath, Ple void p
  | p_top : Ple top top
  
  (* -------- step comparison ------------- *)
      
  | p_step :
      forall (a1 a2 : Axis) (n1 n2 : NodeTest),
      axis_le a1 a2 ->
      ntest_le a2 n1 n2 ->
      Ple (a1:::n1) (a2:::n2)
      
      (* ---- slash based rules ------ *)
      
| p_desc :
      forall (p1 p2 : XPath) (n2 : NodeTest) (q:XQualif),
      Ple p1 (descendant:::%node()) ->
      Ple p2 (qualif (descendant:::n2) q) ->
      Ple (p1/p2) (qualif (descendant:::n2) q)
      
      (* -------- relative-absolute absolute comparisons -------------------------- *)
  | p_abs:
	forall (p : XPath) (q1 q2:XQualif) (n2 : NodeTest),
	Qipl (path (descendant:::%node()/p)) q1 ->
	Ple p (qualif (descendant:::n2) q2)  ->
	Ple p ((qualif top q1)/(qualif (descendant:::n2) q2))
      (* ----------- *)
|  p_slash :
      forall p11 p12 p21 p22 : XPath,      
      Ple (qualif p11 (#p12))   (qualif p21 (#p22)) ->
      Ple p12 p22 ->
      Ple (p11/p12) (p21/p22)


      
      (* ------- intersection rules -------- *)
  | p_inter_R:
      forall p1 p2 p : XPath,
      Ple p p1 ->
      Ple p p2 ->
      Ple p (inter p1 p2)
  | p_inter_L:
      forall p1 p2 p : XPath,
      Ple p1 p ->
      Ple (inter p1 p2) p
      
      (* ------- union rules -------- *) 
  | p_union_L :
      forall p11 p12 p2 : XPath,
      Ple p11 p2 -> Ple p12 p2 -> Ple (union p11 p12) p2

  | p_union_R :
      forall p1 p21 p22 : XPath,
      Ple p1 p21 -> Ple p1 (union p21 p22)
      
      (* -------- qualif comparison ------------- *)
  | p_qual :
      forall p1 p2 : XPath,
      forall q1 q2 : XQualif,
      Ple p1 p2 -> Qipl q1 q2 -> Ple (qualif p1 q1) (qualif p2 q2)


 
          
with Qipl : XQualif -> XQualif -> Prop :=

  | q_leq (* e1 *) :
      forall p11 p12 p21 p22 : XPath,
      Ple p21 p11 -> Ple p12 p22 -> Qipl (leq p11 p12) (leq p21 p22)

  | q_not (* e2 *): 
      forall q1 q2 : XQualif, Qipl q2 q1 -> Qipl (not q1) (not q2)

  | q_true (* e3a *) : 
      forall q : XQualif, Qipl q _true

  | q_false (* e3b *) : 
      forall q : XQualif, Qipl _false q

  | q_and_L (* e4 *) : 
      forall q11 q12 q2 : XQualif, 
      Qipl q11 q2 -> Qipl (q11 and q12) q2

  | q_and_R (* e5 *) :
      forall q1 q21 q22 : XQualif,
      Qipl q1 q21 -> Qipl q1 q22 -> 
      Qipl q1 (q21 and q22)

  | q_or_R (* e6 *) : 
      forall q1 q21 q22 : XQualif, 
      Qipl q1 q21 -> 
      Qipl q1 (q21 or q22)

  | q_or_L (* e7 *) :
      forall q11 q12 q2 : XQualif,
      Qipl q11 q2 -> Qipl q12 q2 ->
      Qipl (q11 or q12) q2

(*      
  | f2 :
      forall (p1 p2 : XPath) (q1 q2 : XQualif),
      Qipl (leq p1 void) (leq p2 void) ->
      Qipl (leq (qualif p1 q1) void) (leq (qualif p2 q2) void)
  | f3 :
      forall (p1 p2 : XPath) (q1 q2 : XQualif),
      Ple p1 p2 ->
      Qipl (not q1) (not q2) ->
      Qipl (leq (qualif p1 q1) void) (leq (qualif p2 q2) void)
*)
  | q_child_desc (* f4 *) :
      forall nt : NodeTest,
	(ntest_le descendant nt _element) ->
      Qipl (leq (step child _any) void) (leq (step descendant nt) void)
      
  
      (* the corresponding propositional equality *)
with Peq : XPath -> XPath -> Prop :=

  |  p_eq : forall p1 p2 : XPath, Ple p1 p2 -> Ple p2 p1 -> Peq p1 p2
.

 
     


Notation "p1 ≤ p2" := (Ple p1 p2) (at level 90, no associativity) : Xrel.
Notation "q1 ⇨ q2" := (Qipl q1 q2) (at level 90, no associativity) : Xrel.
Notation "p1 ≈ p2" := (Peq p1 p2) (at level 90, no associativity) : Xrel.


Open Scope Xp.
Open Scope Xrel.

 (*======= generic usage of equiv ======= *)
Axiom p_gene_L  :
      forall p1 p3:XPath,
      (exists p2:XPath,   (p1 ⇾ p2)    /\   ( p2 ≤ p3) ) ->
      p1 ≤ p3
      .

Axiom p_gene_R  : 
      forall p1 p3:XPath,
      (exists p2:XPath,   (p3 ⇾ p2)   /\    (p1 ≤ p2) ) ->
      p1 ≤ p3
	.

Axiom q_gene_L : 
      forall q1 q3:XQualif,
      (exists q2:XQualif, (q1 ⇐⇒ q2)   /\   (q2 ⇨ q3) ) ->
      q1 ⇨ q3
	.
      
Axiom q_gene_R :
      forall q1 q3:XQualif,
      (exists q2:XQualif,  (q3 ⇐⇒ q2)  /\  (q1 ⇨ q2) ) ->      
      q1 ⇨ q3
	.
     
Definition ple_reflexive (p1 p2:XPath):Prop :=     p1=p2 -> p1 ≤ p2.
Definition qipl_reflexive (q1 q2:XQualif):Prop :=  q1=q2 -> q1 ⇨ q2.

Ltac t1 :=
   match goal with  IHn1:_ |- _ =>
   simpl in |- *;
     intro p2; case p2; simpl in |- *;
     [
	   intro; apply IHn1;auto with arith
	 | intro; apply IHn1; auto with arith
	 | intros; unfold ple_reflexive in |- *; intros; discriminate
	 | intros; unfold ple_reflexive in |- *; intros; discriminate
	 | intros; unfold ple_reflexive in |- *; intros; discriminate
	 | intros; unfold ple_reflexive in |- *; intros; discriminate
	 | intros; unfold ple_reflexive in |- *; intros; discriminate
	 ]
     end.

Ltac redMax H :=
  LeS;
  rewrite max_idem in H;
  rewrite max_idem;
      apply H 
  ||  (match goal with  
      H:max ?a ?b <= ?n |- ?a <= ?n  => eapply max_le_L
      |  H:max ?a ?b <= ?n |- ?b  <= ?n  => eapply max_le_R
     end;apply H)
  .


Lemma Ple_Qipl_reflexive:
    (forall p1 p2:XPath, (ple_reflexive p1 p2)) /\
    (forall q1 q2:XQualif, (qipl_reflexive q1 q2)).

apply HGen22.
induction n.
 (* base cases *)
 simpl in |- *.
   unfold Hyp22 in |- *.
   split.
  intros p1 p2; case p1; case p2; intros;
   match goal with
   | H:(_ <= 0) |- _ => inversion H
   end.
   unfold ple_reflexive in |- *; intros; constructor.
   unfold ple_reflexive in |- *; intros; discriminate.
   unfold ple_reflexive in |- *; intros; discriminate.
   unfold ple_reflexive in |- *; intros; constructor.
   
  intros q1 q2; case q1; case q2; intros;
   match goal with
   | H:(_ <= 0) |- _ => inversion H
   end.
   unfold qipl_reflexive in |- *; intros; constructor.
   unfold qipl_reflexive in |- *; intros; discriminate.
   unfold qipl_reflexive in |- *; intros; discriminate.
   unfold qipl_reflexive in |- *; intros; constructor.
   
(* Inductive step *)   
unfold Hyp22 in IHn |- *.
   elim IHn; intros IHn1 IHn2.
   clear IHn.
   split.
(* ---- path *)
  intro p1; case p1.
   (* void p2 *)
   t1.
   (* top p2 *)
   t1.
   (* union p2 *)
   unfold ple_reflexive in |- *.
   intros.
   rewrite <- H0.
   rewrite <- H0 in H.
   simpl in H.
   apply p_union_L; [ apply p_union_R | apply p_gene_R;exists (union x0 x);split;[apply red_gen;rewrite Pequiv_symmetric | apply p_union_R ] ].
    (* Ple x x *)
    apply IHn1;[redMax H | reflexivity].
    constructor.
    (* Ple x0 x0 *)
    apply IHn1;[redMax H | reflexivity].
   (* inter p2 *)
   unfold ple_reflexive in |- *.
   intros.
   rewrite <- H0.
   rewrite <- H0 in H.
   simpl in H.
  apply p_inter_R;[apply p_inter_L | apply p_gene_L;exists (inter x0 x);split;[apply red_gen;rewrite Pequiv_symmetric | apply p_inter_L] ].

  apply IHn1;[redMax H | reflexivity].
  constructor.
  apply IHn1;[redMax H | reflexivity].
 
 (* slash p2 *)
  unfold ple_reflexive in |- *.
   intros.
   rewrite <- H0.
   rewrite <- H0 in H.
   simpl in H.
  apply p_slash.
  constructor.
  apply IHn1;[redMax H | reflexivity].
  unfold path;constructor;constructor.
  apply IHn1;[redMax H | reflexivity].
  constructor.
  apply IHn1;[redMax H | reflexivity].

   (* qualif p2 *)
 unfold ple_reflexive in |- *.
   intros.
  rewrite <- H0.
   rewrite <- H0 in H.
  simpl in H.
  apply p_qual;[apply IHn1 | apply IHn2];redMax H || reflexivity.

   (* step p2 *)
unfold ple_reflexive in |- *.
   intros.
  rewrite <- H0.
   rewrite <- H0 in H.
  simpl in H.
 constructor.
   case a;simpl;trivial.
   case n0;simpl;trivial.
  (* ------ qualifiers *)
  intros q1 q2;case q1;unfold qipl_reflexive; intros;inversion H0;rewrite <- H0 in H;clear H0 H1;simpl in H. 
 (* not *)
 constructor;
 apply IHn2;[redMax H | reflexivity].
 (* and *)
  apply q_and_R;[apply q_and_L | apply q_gene_L].
  apply IHn2;[redMax H | reflexivity].
 exists (x0 and x);split;constructor.
  apply IHn2;[redMax H | reflexivity].
(* or *)
apply q_or_L;[apply q_or_R | apply q_gene_R].
  apply IHn2; [redMax H | reflexivity].
 exists (x0 or x);split;[constructor | apply q_or_R ].
  apply IHn2; [redMax H | reflexivity].

 (* leq *)
constructor.
   apply IHn1;[redMax H| reflexivity].
   apply IHn1;[redMax H| reflexivity].
(* _true *)
constructor.
 (* _false *)
constructor.
Qed.


Theorem Ple_reflexive: forall p:XPath, p ≤ p.
assert (H:= Ple_Qipl_reflexive).
elim H;intros H1 H2 p;apply H1.
reflexivity.
Qed.

Theorem Qipl_reflexive: forall q:XQualif, q ⇨ q.
assert (H:= Ple_Qipl_reflexive).
elim H;intros H1 H2 q;apply H2.
reflexivity.
Qed.


Conjecture Ple_transitive: forall p1 p2 p3:XPath, p1 ≤ p2  ->  p2 ≤ p3  ->  p1 ≤ p3.

(* I don't known if this proof has any value...seems too much regular *)
Lemma equiv_eq_sound:
    forall p1 p2:XPath,
    (p1 ⇽⇾ p2)  ->  p1 ≈ p2
    .
intros p1 p2 H.
inversion H;
match goal with 
  |- ?a ≈ ?b => 
  split;[ apply p_gene_L | apply p_gene_R];
  exists b;(split;[apply red_gen;constructor | apply Ple_reflexive ]);trivial
end.
Qed.





