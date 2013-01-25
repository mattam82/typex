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




(* void *)
Ltac void_dec:=
  match goal with
   |- ~ Rp ?t void ?x ?y \/ Rp ?t void ?x ?y
  =>  simpl in |- *; auto
 end.

(* top *)
Ltac top_dec:=
  match goal with
   |- ~ Rp ?t top ?x ?y \/ Rp ?t top ?x ?y
  =>  simpl;  case (s_in y (XTree.roots t x));auto
 end.


(* union *)
Ltac union_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : (forall (h0x h0y : NodeId) (h0t : Tree), ~ Rp h0t ?x0 h0x h0y \/ Rp h0t ?x0 h0x h0y)
   |-  ~ Rp ?t (union ?x ?x0) ?x1 ?y \/ Rp ?t (union ?x ?x0) ?x1 ?y
  =>  simpl in |- *;
   elim (H x1 y t); elim (H0 x1 y t); intros H1 H2; [
  left;
    intro H3;
    elim H3;
   auto;
   auto;
   auto |
  right;
    right; assumption |
  right;
    left; assumption |
  right;
    left; assumption
    ]
 end.




(* inter *)
Ltac inter_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : (forall (h0x h0y : NodeId) (h0t : Tree), ~ Rp h0t ?x0 h0x h0y \/ Rp h0t ?x0 h0x h0y)
   |-  ~ Rp ?t (inter ?x ?x0) ?x1 ?y \/ Rp ?t (inter ?x ?x0) ?x1 ?y
  =>
 simpl in |- *;
   elim (H x1 y t); elim (H0 x1 y t); intros H1 H2; [
  left;
    intro H3;
    elim H3;
    intros H4 H5;
    contradiction |
  left;
    intro H3;
    elim H3;
    intros H4 H5;
    contradiction |
  left;
    intro H3;
    elim H3;
    intros H4 H5; contradiction |
  right;
    split; assumption]
 end.

Definition rq_decidable (q:XQualif):= forall (x : NodeId)(t:Tree), (~Rq t q x) \/ (Rq t q x). 
 



(* slash formulé autrement *)
Lemma s_dec:
forall (A:Type) (x1 y:A)(R1 R2:A->A->Prop),
  (forall (x y :A), ~ R1 x y \/ R1 x y)
  -> (forall (x y : A), ~ R2 x y \/ R2 x y)
->
   ~ (exists z : A, R1 x1 z /\ R2 z y) \/
   (exists z : A, R1 x1 z /\ R2 z y).



(* preuve du slash en terme de slash_dec:
 simpl in |- *.
   assert
    (HZ :=
     slash_dec NodeId x1 y (fun x0 y : NodeId => Rp t x x0 y)
       (fun x y : NodeId => Rp t x0 x y)).
   apply HZ.
   split.
  intros.
    apply (H x2 y0 t).
  intros.
    apply (H0 x2 y0 t).
*)



(* slash *)
Ltac slash_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : (forall (h0x h0y : NodeId) (h0t : Tree), ~ Rp h0t ?x0 h0x h0y \/ Rp h0t ?x0 h0x h0y)
   |-  ~ Rp ?t (slash ?x ?x0) ?x1 ?y \/ Rp ?t (slash ?x ?x0) ?x1 ?y
  =>
 simpl; elim (H x1 y t); elim (H0 _ y t); intros H1 H2; [
  
  
  ]
 end.
 
 
 
(* qualif *)
Ltac qualif_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : rq_decidable ?x0
   |-  ~ Rp ?t (qualif ?x ?x0) ?x1 ?y \/ Rp ?t (qualif ?x ?x0) ?x1 ?y
  =>
  simpl in |- *;
   unfold rq_decidable in H0;
   elim (H0 x1 t); elim (H x1 y t); intros H1 H2; [
  left;
    intro H3;
    elim H3;
    intros H4 H5;
    contradiction |
  left;
    intro H3;
    elim H3;
    intros H4 H5;
    contradiction |
  left;
    intro H3;
    elim H3;
    intros H4 H5;
    contradiction |
  right;
    split; assumption]
 end.
 
 
 
  
(* not *)
Ltac not_dec:=
  match goal with
  H : rq_decidable ?x
   |-   rq_decidable (not ?x)
  =>
 unfold rq_decidable in |- *; unfold rq_decidable in H; simpl in |- *;
   intros x0 t;
   elim (H x0 t); [
  intro HC;
    right; assumption |
  intro HC;
    left;
    simpl in |- *;
    auto ]
 end.
 
 
(* and *)
Ltac and_dec:=
  match goal with
  H : rq_decidable ?x,
  H0 : rq_decidable ?x0
   |-   rq_decidable (and ?x ?x0)
  =>
   unfold rq_decidable in |- *; unfold rq_decidable in H, H0; simpl in |- *;
    intros x1 t; elim (H x1 t); elim (H0 x1 t); intros H1 H2; [
  left; intro H3; elim H3; intros H4 H5; contradiction |
  left; intro H3; elim H3; intros H4 H5; contradiction |
  left; intro H3; elim H3; intros H4 H5; contradiction |
  right; split; assumption]
 end.
 
 
(* or *)
Ltac or_dec:=
  match goal with
  H : rq_decidable ?x,
  H0 : rq_decidable ?x0
   |-   rq_decidable (or ?x ?x0)
  =>
 unfold rq_decidable in |- *; unfold rq_decidable in H, H0; simpl in |- *;
  intros x1 t; elim (H x1 t); elim (H0 x1 t); intros H1 H2; [
  left; intro H3; elim H3; intros H4; contradiction |
  right; right; assumption |
  right; left; assumption |
  right; left; assumption ]
 end.
 
 
 
 (* la preuve du lemme de permutation des quantifs nécessite 
 le tiers exclus  p \/ ~p (qui est un axiome de la logique classique)
 donc il faut trouver une autre méthode plus spécifique que les deux lemmes suivants

 
Lemma manip_quantifs1: forall (A: Type)(w:A)(P : A->Prop),
 (forall z1 : A, exists z2:A, ~(P z2) \/ P z1)
 ->
  (~ (forall z : A, P z)) \/ forall z : A, P z.
  Proof.
  
  Qed.
 
 
  Lemma manip_quantifs2: forall (A: Type)(P1 P2 : A->Prop),
 (forall z1 : A, exists z2:A,
 (~((P1 z2) -> (P2 z2))) \/ ((P1 z1) -> (P2 z1)))
 ->
  (~ (forall z : A, P1 z -> P2 z)) \/ (forall z : A, P1 z -> P2 z).
  Proof.
 intros.
 assert (H2 := manip_quantifs1 A (fun z : A => P1 z -> P2 z)).
 apply (H2 H).
 Qed.
 
 
 Lemma manip_quantifs:
 forall (x x0: XPath)(t:Tree)(x1:NodeId),
 (forall z1 : NodeId, exists z2:NodeId,
 (~(Rp t x x1 z2 -> Rp t x0 x1 z2)) \/ (Rp t x x1 z1 -> Rp t x0 x1 z1))
 ->
  (~ (forall z : NodeId, Rp t x x1 z -> Rp t x0 x1 z) \/
 (forall z : NodeId, Rp t x x1 z -> Rp t x0 x1 z)).
 Proof.
 intros.
 assert
 (H2 :=
  manip_quantifs2 NodeId (fun z : NodeId => Rp t x x1 z)
    (fun z : NodeId => Rp t x0 x1 z)).
 apply H2.
 assumption.
 Qed.
 
 Ltac leq_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : (forall (h0x h0y : NodeId) (h0t : Tree), ~ Rp h0t ?x0 h0x h0y \/ Rp h0t ?x0 h0x h0y)
 |-  rq_decidable (leq ?x ?x0)
  =>
  unfold rq_decidable in |- *;
   intros x1 t;
   simpl in |- *;
   apply manip_quantifs;
   intro z1;
   elim (H0 x1 z1 t); elim (H x1 z1 t); intros H1 H2; exists z1; [
    right; intro; contradiction |
    left; intro H3; apply H2; apply H3; assumption |
    right; intro; contradiction |
    right; intro; assumption]
 end.
 
 *)
 
 
 
 
 
 
 
 Lemma move_quantif1:
 (forall (A:Type)(P:A->Prop)(Q:Prop),
 (Q \/ forall z:A, (P z)) ->  forall (z:A), Q \/ (P z)). 
 Proof.
 intros;elim H; [intro; left; assumption |intro H2; right; apply (H2 z)].
Qed.
 

 Lemma move_quantif2:
 (forall (A:Type)(P:A->Prop)(Q:Prop),
forall (z:A), Q /\(P z)->   (Q /\ forall z:A, (P z)) ). 




assert (move_quantif1 NodeId (fun z=>Rp t x x1 z -> Rp t x0 x1 z)
((exists z : NodeId, ~ (Rp t x x1 z -> Rp t x0 x1 z)))).
 
 
assert (forall z : NodeId, (exists z2 : NodeId, ~ (Rp t x x1 z2 -> Rp t x0 x1 z2)) \/ (Rp t x x1 z -> Rp t x0 x1 z)).
 
 
 
 
 Ltac leq_dec:=
  match goal with
  H : (forall (hx0 hy : NodeId) (ht : Tree), ~ Rp ht ?x hx0 hy \/ Rp ht ?x hx0 hy),
  H0 : (forall (h0x h0y : NodeId) (h0t : Tree), ~ Rp h0t ?x0 h0x h0y \/ Rp h0t ?x0 h0x h0y)
 |-  rq_decidable (leq ?x ?x0)
  =>
 unfold rq_decidable in |- *; intros x1 t; simpl in |- *; idtac.
   assert
    ((exists z : NodeId, ~ (Rp t x x1 z -> Rp t x0 x1 z)) \/
     (forall z : NodeId, Rp t x x1 z -> Rp t x0 x1 z)).
  assert
   (forall z : NodeId,
    (exists z2 : NodeId, ~ (Rp t x x1 z2 -> Rp t x0 x1 z2)) \/
    (Rp t x x1 z -> Rp t x0 x1 z)).
   intros.
     <Your Tactic Text here>
   <Your Tactic Text here>
  elim H1; intros H1E.
   left.
     intro.
     elim H1E.
     intros.
     assert (H4 := H2 x2).
     contradiction.
   right; assumption.
 <Your Tactic Text here>
 <Your Tactic Text here>
end.

 
 (* _true *)
Ltac _true_dec:=
  match goal with
   |-    rq_decidable _true
  =>
 unfold rq_decidable in |- *;
   intros x t;
   right;
   simpl in |- *;
   auto
end.
 
 
 (* _false *)
Ltac _false_dec:=
  match goal with
   |-    rq_decidable _false
  =>
 unfold rq_decidable in |- *;
   intros x t;
   left;
   intro H;
   simpl in H;
   contradiction
end. 
 

Theorem rp_decidable: forall (p:XPath)(x y : NodeId)(t:Tree), (~Rp t p x y) \/ (Rp t p x y).
Proof.
intro p.
pattern p in |- *.
apply XJ1 with rq_decidable; intros.
void_dec.
top_dec.
union_dec.
inter_dec.
(* slash_dec. ???*)
qualif_dec.
(* step_dec. ???*)
not_dec.
and_dec.
or_dec.
leq_dec.
_true_dec.
_false_dec.
Qed.
 
 






(* Denotational Seman dec *)


Definition semanQ_deci (q : XQualif):= forall (t : Tree)  (env : Phi)(x : NodeId),
(semanQ env t q x) =true  \/  (semanQ env t q x) =  false .


Lemma semanS_dec: forall (p : XPath)  (env : Phi) (t : Tree) (x y : NodeId),
ZSet.s_in y (semanS env t p x)=true  \/  ZSet.s_in y (semanS env t p x)=false.
Proof.
intro p.
pattern p in |- *.
apply XJ1 with semanQ_deci.
 


Lemma semanS_dec: forall (p : XPath) (env : Phi) (t : Tree) (x y : NodeId),
ZSet.s_in y (semanS env t p x)=true  \/  ZSet.s_in y (semanS env t p x)=false.
Proof.
intro p.
pattern p in |- *.
apply XJ1 with semanQ_deci.
 


(* Containment dec *)

Definition semanQ_deci (q : XQualif):= forall (t : Tree)  (env : Phi)(x : NodeId),
(semanQ env t q x) =true .... (semanQ env t q x) =  false .


Lemma containment_dec: forall (p1 p2 : XPath)  (env : Phi) (t : Tree) (x : NodeId),
ZSet.incl (semanS env t p1 x) (semanS env t p2 x)=true  \/  ZSet.incl (semanS env t p1 x) (semanS env t p2 x)=false.
Proof.
intro p1.
pattern p1 in |- *.
apply XJ1 with semanQ_deci.
 
 
 
 (* slash *)
 intros.
   simpl in |- *.
   induction (semanS env t x x1).
  simpl in |- *.
    left.
    simpl in |- *.
 
 
 
 
 
 (* containment dec avec sem logique *)
 
Definition containment_dec_forQ (q1 : XQualif):= forall (q2: XQualif) (t : Tree) (x : NodeId),
(Rq t q1 x -> Rq t q2 x) /\ ~(Rq t q1 x -> Rq t q2 x).
 
 Theorem containment_dec2: forall (p1 p2:XPath)(x y : NodeId)(t:Tree), 
 (Rp t p1 x y -> Rp t p2 x y) \/ ~(Rp t p1 x y -> Rp t p2 x y).
 Proof.
 intro p1.
pattern p1 in |- *.
apply XJ1 with containment_dec_forQ.
 
 
 
 
 
 