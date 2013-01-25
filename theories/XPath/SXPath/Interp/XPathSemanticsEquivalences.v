(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import XPathSemantics.
Require Import graphInt.
Require Export genSets.
Require Export genSetsInt.
Require setOrder.


Lemma incl_in: forall (a b : NodeSet),
 ZSet.incl a b = true ->
 (forall z:NodeId, s_in z a =true -> s_in z b = true).
 Proof.
 intros a b; assert (HI := ZSet.in_incl a b); elim HI; intros HI1 HI2; apply HI2.
 Qed.

Lemma in_incl: forall (a b : NodeSet),
 (forall z:NodeId, s_in z a =true -> s_in z b = true) -> ZSet.incl a b = true.
 Proof.
 intros a b; assert (HI := ZSet.in_incl a b); elim HI; intros HI1 HI2; apply HI1.
 Qed.

Lemma discri :  forall y : NodeId, s_in y emptyNS = true -> False.
Proof.
intros y H;assert (HC := ZSet.in_sem1 y);unfold emptyNS in H;unfold s_in in H;rewrite HC in H; discriminate.
Qed.

(* Decidability of Interpretations *)
 
Lemma semanQ_decidable: forall (x : NodeId)(q:XQualif)(t:Tree)(env:Phi),
 {semanQ env t q x = true} + {semanQ env t q x = false}.
 Proof.
 induction q; intros.
 elim (IHq t env); intros.
  right.
    simpl in |- *.
    rewrite a.
    reflexivity.
  left.
    simpl in |- *; rewrite b.
    reflexivity.
 elim (IHq1 t env); elim (IHq2 t env); intros.
  left; simpl in |- *; rewrite a; rewrite a0; reflexivity.
  right; simpl in |- *; rewrite a; rewrite b; reflexivity.
  right; simpl in |- *; rewrite a; rewrite b; reflexivity.
  right; simpl in |- *; rewrite b; rewrite b0; reflexivity.
 elim (IHq1 t env); elim (IHq2 t env); intros.
  left; simpl in |- *; rewrite a; rewrite a0; reflexivity.
  left; simpl in |- *; rewrite b; rewrite a; reflexivity.
  left; simpl in |- *; rewrite a; rewrite b; reflexivity.
  right; simpl in |- *; rewrite b0; rewrite b; reflexivity.
 simpl in |- *.
   apply ZSet.incl_dec.
 simpl in |- *.
   left; reflexivity.
 simpl in |- *.
   right; reflexivity.
 Qed.


Axiom test_node_decidable2: forall (x : NodeId)(n:NodeTest)(t:Tree),
 {test_node t n x = true} + {test_node t n x = false}.





(* Required lemma involving set-theoretic 'in' relation *)
 
Axiom in_single1: forall (x y : NodeId), s_in y (single x) = true -> x=y.
Axiom in_single2: forall (x y : NodeId), x=y -> s_in y (single x) = true.



Lemma in_product1: forall (y z: ZSet.A)(s : ZSet.set)(f:ZSet.A->ZSet.set),
s_in z s=true  
-> s_in y (f z) = true
-> s_in y (ZSet.product s f) = true.
Proof.
induction s.
 intros.
   rewrite ZSet.in_sem1 in H; discriminate.
 intros.
   rewrite ZSet.product_sem2.
   cut ({a = z} + {a <> z}).
  intros HC.
    elim HC; intro HC1.
   rewrite <- HC1 in H0.
     apply ZSet.in_unionL.
     assumption.
   apply ZSet.in_unionR.
     apply IHs.
    apply (ZSet.in_sem6 z a s).
     assumption.
     apply sym_not_eq.
       assumption.
    assumption.
  apply Z_eq_dec.
Qed.


Lemma in_product2: forall (y : ZSet.A)(s : ZSet.set)(f:ZSet.A->ZSet.set),
s_in y (ZSet.product s f) = true
-> exists z : ZSet.A, s_in z s=true  /\ s_in y (f z) = true.
Proof.
induction s.
 intros.
   rewrite ZSet.product_empty in H.
   rewrite ZSet.in_sem1 in H; discriminate.
 intros.
   rewrite ZSet.product_sem2 in H.
   cut
    ({s_in y (ZSet.product s f) = true} + {s_in y (ZSet.product s f) = false}).
  intros HC; elim HC; intros HC1.
   elim (IHs f); intros.
    exists x.
      elim H0; intros.
      split.
     apply ZSet.in_sem5.
       assumption.
     assumption.
    assumption.
   exists a.
     split.
    apply ZSet.in_sem2.
    eapply ZSet.in_Lunion.
     apply H.
       apply HC1.
  apply ZSet.in_dec.
Qed.

(*
 SIMPLIFICATION possible: semans.... remplacé par s:set.
*)

Lemma in_qualif1a: forall (y x : NodeId)(p:XPath)(q:XQualif)(t:Tree)(env:Phi),
 s_in y (ZSet.filter (semanS env t p x) (semanQ env t q)) = true ->
   s_in y (semanS env t p x) = true.
   Proof.
intros y x p q t env.
induction (semanS env t p x).
 intros.
   rewrite ZSet.filter_sem3 in H.
   assumption.
 cut ({y = a} + {y <> a}).
  intros HC; elim HC; intros HC1.
   rewrite HC1.
     intros.
     apply ZSet.in_sem2.
   cut ({semanQ env t q a = true} + {semanQ env t q a = false}).
    intros HD; elim HD; intro HD1.
     intros.
       apply ZSet.in_sem5.
       apply IHn.
       rewrite ZSet.filter_sem4 in H.
       rewrite HD1 in H.
       generalize HC1.
       apply ZSet.in_sem6.
       assumption.
     intros.
       rewrite ZSet.filter_sem4 in H.
       rewrite HD1 in H.
       apply ZSet.in_sem5.
       apply IHn.
       assumption.
    apply semanQ_decidable.
  apply Z_eq_dec.
  Qed.
   
   
Lemma in_qualif1b: forall (y x : NodeId)(p:XPath)(q:XQualif)(t:Tree)(env:Phi),
 s_in y (ZSet.filter (semanS env t p x) (semanQ env t q)) = true ->
  semanQ env t q y = true.
  Proof.
intros y x p q t env.
induction (semanS env t p x).
 intros.
   rewrite ZSet.filter_sem3 in H.
   assert (HC := discri y H).
   elim HC.
 intros.
   rewrite ZSet.filter_sem4 in H.
   cut ({semanQ env t q a = true} + {semanQ env t q a = false}).
  intros HC; elim HC; intros HC1.
   rewrite HC1 in H.
     cut ({a = y} + {a <> y}).
    intros HD; elim HD; intros HD1.
     rewrite HD1 in HC1; assumption.
     apply IHn.
       apply (ZSet.in_sem6 y a (ZSet.filter n (semanQ env t q))).
      assumption.
      apply sym_not_eq.
        assumption.
    apply Z_eq_dec.
   rewrite HC1 in H; apply IHn; assumption.
  apply semanQ_decidable.
  Qed.
 

Lemma in_qualif2: forall (y x : NodeId)(p:XPath)(q:XQualif)(t:Tree)(env:Phi),
 s_in y (semanS env t p x) = true ->  semanQ env t q y = true ->
 s_in y (ZSet.filter (semanS env t p x) (semanQ env t q)) = true.
Proof.
intros y x p q t env.
induction (semanS env t p x).
 intros.
   assert (H2 := discri y H); elim H2.
 intros.
   rewrite ZSet.filter_sem4.
   assert ({y = a} + {y <> a}).
  apply Z_eq_dec.
  elim H1; intro H1I.
   rewrite H1I.
     rewrite H1I in H0.
     rewrite H0.
     apply ZSet.in_sem2.
   assert ({semanQ env t q a = true} + {semanQ env t q a = false}).
    apply semanQ_decidable.
    elim H2; intro H2C.
     rewrite H2C.
       apply ZSet.in_sem5.
       apply IHn.
      generalize H1I.
        apply ZSet.in_sem6.
        assumption.
      assumption.
     rewrite H2C.
       apply IHn.
      generalize H1I.
        apply ZSet.in_sem6.
        assumption.
      assumption.
Qed. 
 


(* + demonstrate all ZSet.* used (for now axioms in genSets.v)*)


(* Property used in conjunction with the induction scheme XJ1 *)
Definition sem_equivalence_for_qualifs (q : XQualif) : Prop :=
 forall (x : NodeId) (env : Phi) (t : Tree),
 ((semanQ env t q x)=true <-> (Rq t q x)).


(* Following tactics prove the semantics equivalence*)

(* void *)
Ltac solve_void1 :=
  match goal with
  | id: s_in ?y (semanS ?env ?t void ?x) = true |- _ => simpl in id; assert (HV:s_in y emptyNS = false);[apply ZSet.in_sem1 | rewrite id in HV;discriminate]
 end.

Ltac solve_void2 :=
  match goal with
  | id: Rp ?t void ?x ?y |- _ => auto
end.

(* top*)
Ltac solve_top1 :=
  match goal with
  | id: s_in ?y (semanS ?env ?t top ?x) = true |- _ =>  simpl;simpl in id;assumption
end.

Ltac solve_top2 :=
  match goal with
  | id: Rp ?t top ?x ?y |- _ =>  simpl;simpl in id;assumption
 end.

(* union *)
Ltac solve_union1:=
  match goal with
  | H1: s_in ?y (semanS ?env ?t (union ?x ?x0) ?x1) = true,
     H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
    ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |- Rp ?t (union ?x ?x0) ?x1 ?y
  => simpl in H1; simpl;
 assert (HIN:(s_in y (semanS env t x x1)=true) \/ (s_in y (semanS env t x0 x1)=true));
 [apply ZSet.in_union;assumption |
  elim HIN; [
   intros HIN1;
     left;
     elim (H x1 y env t);
     intros HE1 HE2;
     apply HE1;
     assumption|
   intros HIN1;
     right;
     elim (H0 x1 y env t);
     intros HE1 HE2;
     apply HE1;
     assumption
 ]]
 end.
 

Ltac solve_union2:=
  match goal with
  | H1: Rp ?t (union ?x ?x0) ?x1 ?y,
    H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
   ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |-  s_in ?y (semanS ?env ?t (union ?x ?x0) ?x1) = true
 => simpl; simpl in H1;
   elim H1;intro Rx; [
    apply ZSet.in_unionL;
    elim (H x1 y env t);
    intros HE1 HE2;
    apply HE2;
    assumption |
    apply ZSet.in_unionR;
    elim (H0 x1 y env t);
    intros HE1 HE2;
    apply HE2; assumption]
end.





(* inter *)
Ltac solve_inter1:=
  match goal with
  | H1: s_in ?y (semanS ?env ?t (inter ?x ?x0) ?x1) = true,
     H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
    ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |- Rp ?t (inter ?x ?x0) ?x1 ?y
  => simpl in H1; simpl;
 assert (HIN:(s_in y (semanS env t x x1)=true) /\ (s_in y (semanS env t x0 x1)=true));
 [apply ZSet.in_inter1;assumption |
  elim HIN; intros HA1 HA2;
  elim (H x1 y env t); intros HE1 HE2;
  elim (H0 x1 y env t);  intros HF1 HF2;
  split; [ apply HE1;assumption  | apply HF1;assumption ]
  ]
 end.
 

Ltac solve_inter2:=
  match goal with
  | H1: Rp ?t (inter ?x ?x0) ?x1 ?y,
    H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
   ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |-  s_in ?y (semanS ?env ?t (inter ?x ?x0) ?x1) = true
 => simpl; simpl in H1;
   elim H1;intros HA1 HA2;
    apply ZSet.in_inter2;
    elim (H x1 y env t); intros HE1 HE2;
    elim (H0 x1 y env t); intros HF1 HF2;
    split; [ apply HE2;assumption  | apply HF2;assumption]
end.




(* product *)
Ltac solve_product1:=
  match goal with
  | H1: s_in ?y (semanS ?env ?t (slash ?x ?x0) ?x1) = true,
     H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
    ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |- Rp ?t (slash ?x ?x0) ?x1 ?y
  =>simpl in |- *; simpl in H1;
assert (H2 := in_product2 y (semanS env t x x1) (semanS env t x0) H1);
elim H2;
intros x2 H3;
elim H3; intros H3A H3B;
exists x2;
elim (H x1 x2 env t); intros HE1 HE2;
elim (H0 x2 y env t); intros HF1 HF2;
split; [ apply HE1;assumption | apply HF1;assumption]
end.
 

Ltac solve_product2:=
  match goal with
  | H1: Rp ?t (slash ?x ?x0) ?x1 ?y,
    H: (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
   ,H0:  (forall (hx hy : NodeId) (henv : Phi) (ht : Tree), ((s_in hy (semanS henv ht ?x0 hx) = true) <-> Rp ht ?x0 hx hy))
    |-  s_in ?y (semanS ?env ?t (slash ?x ?x0) ?x1) = true
 => 
  simpl in |- *; simpl in H1;
   elim H1; intros z H2;
   elim (H x1 z env t); intros HE1 HE2;
   elim (H0 z y env t); intros HF1 HF2;
   elim H2; intros H2A H2B;
   apply (in_product1 y z (semanS env t x x1) (semanS env t x0)); [  
   	apply HE2; assumption 
      | apply HF2; assumption]
end.


(* qualif *)
Ltac solve_qualif1:=
  match goal with
  | H1: s_in ?y (semanS ?env ?t (qualif ?x ?x0) ?x1) = true,
    H : (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
   ,H0:  sem_equivalence_for_qualifs ?x0
    |-  Rp ?t (qualif ?x ?x0) ?x1 ?y
 => simpl in |- *; simpl in H1; unfold sem_equivalence_for_qualifs in H0;
   elim (H x1 y env t); intros HE1 HE2; elim (H0 y env t); intros H01 H02;
   split;
    [ apply HE1; apply (in_qualif1a y x1 x x0 t env); assumption
    | apply H01; apply (in_qualif1b y x1 x x0 t env); assumption ]
end.
 
 
 
Ltac solve_qualif2:=
  match goal with
  | H1: Rp ?t (qualif ?x ?x0) ?x1 ?y,
    H : (forall (gx0 gy : NodeId) (genv : Phi) (gt : Tree), ((s_in gy (semanS genv gt ?x gx0) = true) <-> Rp gt ?x gx0 gy))
   ,H0:  sem_equivalence_for_qualifs ?x0
    |-  s_in ?y (semanS ?env ?t (qualif ?x ?x0) ?x1) = true
 =>simpl in |- *;
   simpl in H1;
   unfold sem_equivalence_for_qualifs in H0;
   elim H1; intros HI1 HI2;
   elim (H x1 y env t); intros HE1 HE2;
   elim (H0 y env t); intros H01 H02;
   apply in_qualif2; [  apply HE2; assumption |
   		       apply H02; assumption]
end.




(* TODO *)

(* temporary situation *)

(*Axiom step1: *)
Lemma step1: 
forall (y x: NodeId) (env:Phi) (t:Tree) (a:Axis) (n:NodeTest),
s_in y (semanS env t (step a n) x) = true ->  Rp t (step a n) x y.

Proof.
intros y x env t a n.
case a; simpl in |- *; intros.
(* a=self *)
 assert ({test_node t n x = true} + {test_node t n x = false}).
Admitted.
(*
  <Your Tactic Text here>
  elim H0; intros; split.
   rewrite a0 in H.
     apply in_single.
     assumption.
   rewrite a0 in H.
     assert (HA := in_single x y H).
     rewrite <- HA; assumption.
   rewrite b in H.
     rewrite ZSet.in_sem1 in H.
     discriminate.
   rewrite b in H.
     rewrite ZSet.in_sem1 in H; discriminate.
Qed.     
*)     




Axiom step2: 
forall (y x: NodeId) (env:Phi) (t:Tree) (a:Axis) (n:NodeTest),
 Rp t (step a n) x y -> s_in y (semanS env t (step a n) x) = true.



(* step *)
Ltac solve_step1:=
  match goal with
  | H : s_in ?y (semanS ?env ?t (step ?a ?n) ?x) = true
    |-  Rp ?t (step ?a ?n) ?x ?y
 => apply (step1 y x env t a n); assumption
(*generalize H; clear H;
case a; simpl in |- *; [
 assert (HC : {test_node t n x = true} + {test_node t n x = false}); [
  apply test_node_decidable |
  elim HC; intro H;
   rewrite H;
     intro G;
     split; [
    apply in_single; assumption |
    assert (F : x = y); [
     apply in_single; assumption |
     rewrite <- F;
       assumption] |
    
  ...   
       
]]] *)
 end.


Ltac solve_step2:=
  match goal with
  | H : Rp ?t (step ?a ?n) ?x ?y
    |-  s_in ?y (semanS ?env ?t (step ?a ?n) ?x) = true
 =>apply (step2 y x env t a n); assumption
 
  end.




(* not *)
Ltac solve_not1:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0 : semanQ ?env ?t (not ?x) ?x0 = true
    |-  Rq ?t (not ?x) ?x0
 =>simpl; simpl in H0;
   assert (HD:({semanQ env t x x0 = true} + {semanQ env t x x0 = false})); [
   apply semanQ_decidable |
  intro HC; elim HD; intro HQ; [
   rewrite HQ in H0;
     discriminate
   |unfold sem_equivalence_for_qualifs in H;
     assert (HCP := H x0 env t); elim HCP; intros HE1 HE2;
      assert (H1:(semanQ env t x x0 = true)); [
     apply HE2; auto |
     rewrite H1 in H0; discriminate]
  ]]
  end.



Ltac solve_not2:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0 : Rq ?t (?not ?x) ?x0
    |-  semanQ ?env ?t (not ?x) ?x0 = true
 => simpl; simpl in H0;
    unfold sem_equivalence_for_qualifs in H;
    assert (H1:({semanQ env t x x0 = true} + {semanQ env t x x0 = false})); [
       apply semanQ_decidable |
 elim H1;intro H2; [
   elim H0; elim (H x0 env t);intros H3 H4;apply H3;assumption |
    rewrite H2;reflexivity]
 ]
end.


(* and *)
Ltac solve_and1:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0: sem_equivalence_for_qualifs ?x0,
    H1: semanQ ?env ?t (and ?x ?x0) ?x1 = true
    |-  Rq ?t (and ?x ?x0) ?x1
 => simpl; simpl in H1;
   assert (HC:({semanQ env t x x1 = true} + {semanQ env t x x1 = false})); [
     apply semanQ_decidable  |
	  unfold sem_equivalence_for_qualifs in H, H0;
	   elim HC;intros H2; split; [
	   	elim (H x1 env t);intros H3 H4;apply H3; assumption
	      |	elim (H0 x1 env t);intros H3 H4;apply H3; rewrite H2 in H1;assumption
	      | rewrite H2 in H1;discriminate
	      | rewrite H2 in H1;discriminate]
]
end.


Ltac solve_and2:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0: sem_equivalence_for_qualifs ?x0,
    H1: Rq ?t (and ?x ?x0) ?x1
    |-  semanQ ?env ?t (and ?x ?x0) ?x1 = true
 => simpl; simpl in H1;
   unfold sem_equivalence_for_qualifs in H, H0;
   elim H1; intros H2 H3;
   elim (H x1 env t); intros H4 H5;
   elim (H0 x1 env t); intros H6 H7;
   assert (H8:(semanQ env t x x1)=true); [ apply H5; assumption |
   assert (H9:(semanQ env t x0 x1)=true); [ apply H7; assumption |
   rewrite H8;rewrite H9; reflexivity]]
 end.
 

(* or *)

Ltac solve_or1:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0: sem_equivalence_for_qualifs ?x0,
    H1: semanQ ?env ?t (or ?x ?x0) ?x1 = true
    |-  Rq ?t (or ?x ?x0) ?x1
 => simpl; simpl in H1;   unfold sem_equivalence_for_qualifs in H, H0;
   assert (HP:({semanQ env t x x1 = true} + {semanQ env t x x1 = false})); [
    apply semanQ_decidable |
  elim HP; intro HC; [
     assert (HT := H x1 env t);
    elim HT;
    intros HT1 HT2;
      left;
      apply HT1;
      auto |
   right;
     assert (H0P := H0 x1 env t);
    elim H0P;
      intros HT1 HT2;
      apply HT1;
      rewrite HC in H1; auto
 ]]
 end.



Ltac solve_or2:=
  match goal with
  | H : sem_equivalence_for_qualifs ?x,
    H0: sem_equivalence_for_qualifs ?x0,
    H1: Rq ?t (or ?x ?x0) ?x1
    |-  semanQ ?env ?t (or ?x ?x0) ?x1 = true
 =>  
  simpl; simpl in H1; unfold sem_equivalence_for_qualifs in H, H0;
   assert (HP : {semanQ env t x x1 = true} + {semanQ env t x x1 = false}); [
  apply semanQ_decidable |
  elim HP; intros HC; [
   rewrite HC; auto |
   rewrite HC;
     assert (H0P := H0 x1 env t); elim H0P;
     intros HT1 HT2;
     apply HT2;
     elim H1; intro H1P; [
    elim (H0 x1 env t); intros H01 H02;
      assert (H2:semanQ env t x x1 = true); [
     elim (H x1 env t); intros H11 H12;
       apply H12; assumption |
     rewrite H2 in HC; discriminate] |
    assumption
    ]]]
end.



(* leq *)

Ltac solve_leq1:=
  match goal with
  |  H : forall (hx0 hy : NodeId) (henv : Phi) (ht : Tree),
         s_in hy (semanS henv ht ?x hx0) = true <-> Rp ht ?x hx0 hy,
     H0 : forall (h0x h0y : NodeId) (h0env : Phi) (h0t : Tree),
         s_in h0y (semanS h0env h0t ?x0 h0x) = true <-> Rp h0t ?x0 h0x h0y,
     H1 : semanQ ?env ?t (leq ?x ?x0) ?x1 = true
    |-   Rq ?t (leq ?x ?x0) ?x1
 => simpl; simpl in H1;
   assert (HI := incl_in (semanS env t x x1) (semanS env t x0 x1));
   assert (HIC := HI H1);
   intros z H2;
   assert (HIC2 := HIC z);
   elim (H0 x1 z env t);
   intros HE1 HE2;
   apply HE1;
   apply HIC2;
   elim (H x1 z env t);
   intros HT1 HT2;
   apply HT2;
   assumption
 end.



Ltac solve_leq2:=
  match goal with
  |  H : forall (hx0 hy : NodeId) (henv : Phi) (ht : Tree),
         s_in hy (semanS henv ht ?x hx0) = true <-> Rp ht ?x hx0 hy,
     H0 : forall (h0x h0y : NodeId) (h0env : Phi) (h0t : Tree),
         s_in h0y (semanS h0env h0t ?x0 h0x) = true <-> Rp h0t ?x0 h0x h0y,
     H1 :  Rq ?t (leq ?x ?x0) ?x1
    |-  semanQ ?env ?t (leq ?x ?x0) ?x1 = true
 =>  
  simpl; simpl in H1;
  apply in_incl;
  intros z H2;
  assert (H3 := H1 z);
  elim (H0 x1 z env t);
  intros HE1 HE2;
  apply HE2;
  apply H3;
  elim (H x1 z env t);
  intros HT1 HT2;
  apply HT1;
  assumption
end.


(* Denotational and Relational Semantics are equivalent *)
Require Import XPathGrammar.
Theorem sem_equivalence:
 forall (p : XPath) (x y : NodeId) (env : Phi) (t : Tree),
 s_in y (semanS env t p x)=true <-> Rp t p x y.
Proof.
intro p.
pattern p in |- *.
apply XJ1 with sem_equivalence_for_qualifs; intros; split;intros.
  solve_void1.
  solve_void2.
  solve_top1.
  solve_top2.
  solve_union1.
  solve_union2.
  solve_inter1.
  solve_inter2.
  solve_product1.
  solve_product2.
  solve_qualif1.
  solve_qualif2.
  solve_step1.
  solve_step2.
  solve_not1.
  solve_not2.
  solve_and1.
  solve_and2.
  solve_or1.
  solve_or2.
  solve_leq1.
  solve_leq2.
 (* _true *)
 solve [simpl;auto].
 solve [simpl;reflexivity].
 (* _false *)
 solve [simpl in H;auto;discriminate].
 solve [simpl in H;auto].
 Qed.





