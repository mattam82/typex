(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import Bool.

Module Type CmpOrderTheory.

Parameter A : Set.
Parameter le : A -> A -> bool.

(* properties *)
Parameter le_reflexive : forall x : A, le x x = true.
Parameter le_asymmetric : forall x y : A, le x y = false -> le y x = true.
Parameter
  le_antisymmetric : forall x y : A, le x y = true -> le y x = true -> x = y.
Parameter
  le_transitive :
    forall (b : bool) (x y z : A), le x y = b -> le y z = b -> le x z = b.
Parameter le_dec : forall x y : A, {le x y = true} + {le x y = false}.


Parameter lt : A -> A -> bool.


Axiom lt_le : forall x y : A, lt x y = true -> le x y = true.
Axiom
  lt_le_nle :
    forall x y : A, lt x y = true -> le x y = true /\ le y x = false.
Axiom lt_not_le : forall (b : bool) (x y : A), lt x y = b <-> le y x = negb b.
Axiom lt_not_le_false : forall x y : A, lt x y = true -> le y x = false.
Axiom lt_not_le_true : forall x y : A, lt x y = false -> le y x = true.
Axiom lt_asymmetric : forall x y : A, lt x y = true -> lt y x = false.
Axiom lt_areflexive : forall x : A, lt x x = false.
Axiom
  lt_transitive :
    forall x y z : A, lt x y = true -> lt y z = true -> lt x z = true.
Axiom
  lt_le_transitive :
    forall x y z : A, lt x y = true -> le y z = true -> lt x z = true.

Parameter eq : A -> A -> bool.

Axiom eq_reflexive : forall x : A, eq x x = true.
Axiom eq_symmetric : forall x y : A, eq x y = true -> eq y x = true.
Axiom eq_symm2 : forall x y : A, eq x y = false -> eq y x = false.
Axiom eq_commutative : forall x y : A, eq x y = eq y x.
Axiom eq_neg_le : forall x y : A, eq x y = false -> le x y = negb (le y x).
Axiom eq_le1 : forall x y : A, eq x y = true -> le x y = true.
Axiom eq_le2 : forall x y : A, eq x y = true -> le y x = true.
Axiom
  eq_trans :
    forall x y z : A, eq x y = true -> eq y z = true -> eq x z = true.
Axiom eq_dec : forall a b : A, {eq a b = true} + {eq a b = false}.
Axiom eq_neg1 : forall x y : A, eq x y <> true -> eq x y = false.
Axiom eq_neg2 : forall x y : A, eq x y = false -> eq x y <> true.
Axiom eq_neg : forall x y : A, eq x y = false <-> eq x y <> true.
Axiom eq_pos1 : forall x y : A, eq x y <> false -> eq x y = true.
Axiom eq_pos2 : forall x y : A, eq x y = true -> eq x y <> false.
Axiom eq_pos : forall x y : A, eq x y = false <-> eq x y <> true.

Axiom eq_eq : forall x y : A, eq x y = true -> x = y.
Axiom eq_neq : forall x y : A, eq x y = false -> x <> y.



Axiom
  le_nle_neq :
    forall x y : A, le x y = false -> le y x = true -> eq x y = false.
Axiom
  neq_le_le :
    forall x y : A, eq x y = false -> le x y = true -> le y x = false.
Axiom
  neq_le_lt :
    forall x y : A, eq x y = false -> le x y = true -> lt x y = true.
Axiom
  eq_lt : forall x y : A, eq x y = false -> lt x y = true \/ lt y x = true.


End CmpOrderTheory.



Module Type PartialReflexiveOrder.
(* =====================================================================================*)
(* Inputs and hypotheses *)
(* =====================================================================================*)

Parameter A : Set.
Parameter A_le : A -> A -> bool.

(* properties *)
Axiom reflexive : forall x : A, A_le x x = true.
Axiom
  antisymmetric : forall x y : A, A_le x y = true -> A_le y x = true -> x = y.
Axiom
  transitive :
    forall (b : bool) (x y z : A),
    A_le x y = b -> A_le y z = b -> A_le x z = b.
Axiom dec : forall x y : A, {A_le x y = true} + {A_le x y = false}.

End PartialReflexiveOrder.



Module Type ReflexiveOrder.
(* =====================================================================================*)
(* Inputs and hypotheses *)
(* =====================================================================================*)

Parameter A : Set.
Parameter A_le : A -> A -> bool.

(* properties *)
Axiom reflexive : forall x : A, A_le x x = true.
Axiom asymmetric : forall x y : A, A_le x y = false -> A_le y x = true.
Axiom
  antisymmetric : forall x y : A, A_le x y = true -> A_le y x = true -> x = y.
Axiom
  transitive :
    forall (b : bool) (x y z : A),
    A_le x y = b -> A_le y z = b -> A_le x z = b.
Axiom dec : forall x y : A, {A_le x y = true} + {A_le x y = false}.

End ReflexiveOrder.



Module Type DecidableEquality.
(* =====================================================================================*)
(* Inputs and hypotheses *)
(* =====================================================================================*)

Parameter A : Set.
Parameter A_eq : A -> A -> bool.

(* properties *)
Axiom reflexive : forall x : A, A_eq x x = true.
Axiom symmetric : forall x y : A, A_eq x y = true -> A_eq y x = true.
Axiom eq_struct : forall x y : A, A_eq x y = true -> x = y.
Axiom
  transitive :
    forall x y z : A, A_eq x y = true -> A_eq y z = true -> A_eq x z = true.
Axiom dec : forall x y : A, {A_eq x y = true} + {A_eq x y = false}.

End DecidableEquality.




Module cmpOrder (reflexiveOrder: ReflexiveOrder) : CmpOrderTheory with
  Definition A := reflexiveOrder.A.

(* =====================================================================================*)
(* Inputs and hypotheses *)
(* =====================================================================================*)

Definition A := reflexiveOrder.A.
Definition le := reflexiveOrder.A_le.

(* properties *)
Definition le_reflexive := reflexiveOrder.reflexive.
Definition le_asymmetric := reflexiveOrder.asymmetric.
Definition le_antisymmetric := reflexiveOrder.antisymmetric.
Definition le_transitive := reflexiveOrder.transitive.
Definition le_dec := reflexiveOrder.dec.


(* =====================================================================================*)
(* end hypotheses *)
(* =====================================================================================*)




(* =====================================================================================*)
Section equality.

Definition eq (x y : A) : bool := if le x y then le y x else false.

Theorem eq_reflexive : forall x : A, eq x x = true.
Proof.
intro x; unfold eq in |- *.
cut (le x x = true);
 [ intro H; rewrite H; compute in |- *; reflexivity | apply le_reflexive ].
Qed.

Theorem eq_symmetric : forall x y : A, eq x y = true -> eq y x = true.
Proof.
intros x y.
unfold eq in |- *.
case (le x y).
intro H; rewrite H; compute in |- *; reflexivity.

intro H; elimtype False; discriminate H.
Qed.

Theorem eq_symm2 : forall x y : A, eq x y = false -> eq y x = false.
Proof.
intros x y.
unfold eq in |- *.
case (le x y).
intro H; rewrite H; compute in |- *; reflexivity.

intro H; case (le y x); [ reflexivity | reflexivity ].
Qed.

Theorem eq_commutative : forall x y : A, eq x y = eq y x.
Proof.
intros x y.
unfold eq in |- *.
case (le x y);
 [ case (le y x); [ reflexivity | reflexivity ]
 | case (le y x); [ reflexivity | reflexivity ] ].
Qed.


Theorem eq_neg_le : forall x y : A, eq x y = false -> le x y = negb (le y x).
Proof.
intros x y H.
cut ({le x y = true} + {le x y = false}).
intro H1; elim H1.
intro H2.
rewrite H2.
unfold eq in H.
rewrite H2 in H.
rewrite H.
reflexivity.

intro H2. 
rewrite H2.
assert (H3 := le_asymmetric x y H2).
compute in |- *. 
rewrite H3. 
reflexivity.

apply le_dec.
Qed.


Theorem eq_le1 : forall x y : A, eq x y = true -> le x y = true.
Proof.
intros x y.
compute in |- *.
case reflexiveOrder.A_le.
	intro; reflexivity.
	intro; discriminate.
Qed.


Theorem eq_le2 : forall x y : A, eq x y = true -> le y x = true.
Proof.
intros x y.
compute in |- *.
case reflexiveOrder.A_le.
	intro; assumption.
	intro; discriminate.
Qed.



Theorem eq_eq : forall x y : A, eq x y = true -> x = y.
Proof.
intros.
apply le_antisymmetric;
 [ generalize H; compute in |- *; case reflexiveOrder.A_le; auto; auto
 | generalize H; compute in |- *; case reflexiveOrder.A_le; auto; intro;
    discriminate ].
Qed.



Theorem eq_trans :
 forall x y z : A, eq x y = true -> eq y z = true -> eq x z = true.
Proof.
intros x y z H1 H2.
unfold eq in |- *.
cut (le x z = true /\ le z x = true).
intro H3; elim H3; intros H4 H5.
rewrite H4; assumption.

split.
apply (le_transitive true) with (y := y).
apply eq_le1.
assumption.

apply eq_le1.
assumption.

assert (y = z).
apply eq_eq.
assumption.

subst.
apply eq_le2.
assumption.

Qed.



Hint Resolve eq_reflexive eq_symmetric eq_symm2 eq_commutative: datatypes.


Theorem eq_dec : forall a b : A, {eq a b = true} + {eq a b = false}.
Proof.
intros a b.
cut ({le a b = true} + {le a b = false}).
  intro H.
  unfold eq in |- *.
  compute in |- *.
  elim H;
   [ intro H1; compute in H1; rewrite H1; apply le_dec
   | intro H1; compute in H1; rewrite H1; right; reflexivity ].
	
  apply le_dec.
Qed.




Theorem eq_neg1 : forall x y : A, eq x y <> true -> eq x y = false.
Proof.
intros x y; unfold eq in |- *.
case (le x y);
 [ intro H; compute in H; cut ({le y x = true} + {le y x = false});
    [ intro H1; elim H1; [ intro H2; elimtype False; exact (H H2) | trivial ]
    | apply le_dec ]
 | intro; trivial ].
Qed.




Theorem eq_neg2 : forall x y : A, eq x y = false -> eq x y <> true.
Proof.
intros x y.
unfold eq in |- *.
case (le x y).
intro H.
compute in |- *.
intro H1.
compute in H.
rewrite H in H1.
discriminate.
intro.
compute in |- *.
discriminate.
Qed.

Hint Resolve eq_neg1 eq_neg2: datatypes.

Theorem eq_neg : forall x y : A, eq x y = false <-> eq x y <> true.
Proof.
intros x y.
split.
apply eq_neg2.
apply eq_neg1.
Qed.


Theorem eq_pos1 : forall x y : A, eq x y <> false -> eq x y = true.
Proof.
intros x y; unfold eq in |- *.
case (le x y).
case (le y x).
intro; reflexivity.

intro H; elimtype False; apply H; reflexivity.

intro H; elimtype False; apply H; reflexivity.
Qed.

Theorem eq_pos2 : forall x y : A, eq x y = true -> eq x y <> false.
Proof.
intros x y.
unfold eq in |- *.
case (le x y).
case (le y x).
intros H1 H2.
discriminate H2.

intros H1 H2.
discriminate H1.

intros H1 H2.
discriminate H1.
Qed.

Hint Resolve eq_pos1 eq_pos2: datatypes.



Theorem eq_pos : forall x y : A, eq x y = false <-> eq x y <> true.
Proof.
intros x y; split; auto.
intro.
apply eq_neg2.
assumption.

intro.
apply eq_neg1.
assumption.
Qed.




Theorem eq_neq : forall x y : A, eq x y = false -> x <> y.
Proof.
intros x y H.
red in |- *.
intro H1; rewrite H1 in H.
assert (H2 := eq_reflexive y).
rewrite H2 in H; discriminate H.
Qed.


Hint Resolve eq_neq: datatypes.





End equality.
(* =====================================================================================*)



(* =====================================================================================*)
Section A_strictOrder.

Definition lt (x y : A) : bool := if le y x then false else true.

Theorem lt_le : forall x y : A, lt x y = true -> le x y = true.
Proof.
intros x y.
unfold lt in |- *.
intro H.
cut (le y x = false).
apply le_asymmetric with (x := y) (y := x).

simplify_eq H.
case (le y x).
apply sym_eq.

intro; reflexivity.
Qed.


Theorem lt_le_nle :
 forall x y : A, lt x y = true -> le x y = true /\ le y x = false.
Proof.
intros x y.
intro H; split;
 [ apply lt_le; exact H
 | unfold lt in H; simplify_eq H; case (le y x);
    [ intro H1; discriminate H1 | intro H1; reflexivity ] ].
Qed.


Theorem lt_not_le :
 forall (b : bool) (x y : A), lt x y = b <-> le y x = negb b.
Proof.
intros b x y.
case b.
split.
intro H.
compute in |- *.
assert (H1 := lt_le_nle x y H); elim H1.
intros H2 H3.
exact H3.

compute in |- *; intro H; compute in H; rewrite H; reflexivity.

split.
compute in |- *; case (le y x).
intro.
generalize H.
case reflexiveOrder.A_le.
trivial.

intro; discriminate.

case reflexiveOrder.A_le.
trivial.

intro; discriminate.

compute in |- *.
intro.
rewrite H.
trivial.
Qed.



Theorem lt_not_le_false : forall x y : A, lt x y = true -> le y x = false.
Proof.
intros x y.
assert (H := lt_not_le true x y).
intro H1.
elim H.
intros H2 H3.
exact (H2 H1).
Qed.

Theorem lt_not_le_true : forall x y : A, lt x y = false -> le y x = true.
Proof.
intros x y.
assert (H := lt_not_le false x y).
intro H1.
elim H.
intros H2 H3.
exact (H2 H1).
Qed.



Theorem lt_asymmetric : forall x y : A, lt x y = true -> lt y x = false.
Proof.
intros x y.
unfold lt in |- *.
cut ({le x y = true} + {le x y = false}).
intro H; elim H.
intro H1; rewrite H1.
intro; reflexivity.

intro H1; rewrite H1.
cut (le y x = true).
intro H2; rewrite H2.
intro H3; discriminate H3.

apply le_asymmetric.
exact H1.

apply le_dec.
Qed.


Theorem lt_areflexive : forall x : A, lt x x = false.
Proof.
intro x; unfold lt in |- *; rewrite le_reflexive; reflexivity.
Qed.


Theorem lt_transitive :
 forall x y z : A, lt x y = true -> lt y z = true -> lt x z = true.
Proof.
intros x y z H1 H2.
compute in |- *.
cut (le x z = true /\ le z x = false).
intro H3; elim H3; intros H4 H5; compute in H5; rewrite H5; reflexivity.
split.
apply (le_transitive true) with (y := y).
apply lt_le; exact H1.
apply lt_le; exact H2.
apply (le_transitive false) with (y := y).
apply lt_not_le_false; exact H2.
apply lt_not_le_false; exact H1.
Qed.


(* I found this one impossible to prove without tne antisymmetry of le *)
Theorem lt_le_transitive :
 forall x y z : A, lt x y = true -> le y z = true -> lt x z = true.
Proof.
intros x y z H1 H2.
cut ({eq y z = true} + {eq y z = false}).
intro H; elim H.
intro H3.
cut (y = z).
intro H4; rewrite H4 in H1; exact H1.

apply le_antisymmetric.
exact H2.

unfold eq in H3.
simplify_eq H3.
case (le y z).
trivial.

intro H4; discriminate H4.

intro H3.
compute in |- *.
cut (le z x = false).
intro H4; compute in H4; rewrite H4; reflexivity.

apply (le_transitive false) with (y := y).
unfold eq in H3.
rewrite H2 in H3.
exact H3.

apply lt_not_le_false; exact H1.

apply eq_dec.
Qed.





Theorem le_nle_neq :
 forall x y : A, le x y = false -> le y x = true -> eq x y = false.
Proof.
intros.
unfold eq in |- *.
rewrite H.
reflexivity.
Qed.






Theorem neq_le_le :
 forall x y : A, eq x y = false -> le x y = true -> le y x = false.
Proof.
intros.
unfold eq in H.
rewrite H0 in H.
assumption.
Qed.



Theorem neq_le_lt :
 forall x y : A, eq x y = false -> le x y = true -> lt x y = true.
Proof.
intros.
compute in |- *.
assert (le y x = false).
apply neq_le_le.
assumption.

assumption.

compute in H1; rewrite H1.
reflexivity.
Qed.




Theorem eq_lt :
 forall x y : A, eq x y = false -> lt x y = true \/ lt y x = true.
Proof.
intros.
assert ({le x y = true} + {le x y = false}).
apply le_dec.

elim H0.
intro.
left.
apply neq_le_lt.
assumption.

assumption.

intro.
right.
apply neq_le_lt.
apply eq_symm2.
assumption.

apply le_asymmetric.
assumption.
Qed.





Hint Resolve lt_asymmetric lt_areflexive lt_transitive: datatypes.

End A_strictOrder.
End cmpOrder.
