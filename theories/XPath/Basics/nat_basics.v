(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)


(* basic lemmas on natural operations *)
(* December, 2003 *)
(* $Header: /local_home/cvs/cvs-base/XPathCoq/v8/Basics/nat_basics.v,v 1.7 2004/09/30 14:54:39 cvs Exp $
   $Log: nat_basics.v,v $
   Revision 1.7  2004/09/30 14:54:39  cvs
   Added banners.

   Revision 1.6  2004/09/01 08:14:50  cvs
   update

   Revision 1.5  2004/05/05 14:30:15  cvs
   fix v8.2 syntactic incompatibilities + changed name matching in SemanS (XPathSemantics.v)

   Revision 1.4  2004/04/23 10:13:10  cvs
   *** empty log message ***

   Revision 1.3  2004/04/22 14:35:31  cvs
   *** empty log message ***

   Revision 1.2  2004/04/20 14:22:06  cvs
   SXPath/Containment/XPCcomplete.v

   Revision 1.1  2004/03/31 13:08:26  cvs
   translated to v8

   Revision 1.1  2004/03/31 09:49:50  cvs
   *** empty log message ***

   Revision 1.2  2003/12/09 16:05:21  cvs
   added cvs log

 *)
Require Export Max.
Require Export Le.
Require Export Plus.
Require Export Bool.


(* Some useful nat related lemma used for inductive proofs on 
numerical hypotheses CXP and CXQ *)

Lemma plus_m_n_O : forall m n : nat, m + n = 0 -> m = 0 /\ n = 0.
simple induction m.
simpl in |- *.
auto.

intros n H.
intros.
rewrite plus_Sn_m in H0.
discriminate.
Qed.


Lemma plus_m_S : forall m n : nat, m + S n = S (m + n).
simple induction m.
simpl in |- *.
auto.

simpl in |- *.
intros n H n0.
rewrite H.
auto.
Qed.

Axiom Eq_P_Q : forall P Q : Prop, (P -> Q) -> (Q -> P) -> P = Q.


Lemma le_S_S : forall m n : nat, (S m <= S n) = (m <= n).
intros m n; apply Eq_P_Q.
intro.
apply le_S_n.
auto.

intro; apply le_n_S; auto.
Qed.


Lemma max_le_r : forall m n : nat, max m n = n -> m <= n.
double induction m n.
auto.

auto.

simpl in |- *.
intros.
rewrite H0; trivial.

intros.
apply le_n_S.
apply H0.
cut (max (S n1) (S n) = S (max n1 n)).
intro H2; rewrite H2 in H1.
injection H1.
trivial.

symmetry  in |- *.
apply max_SS.
Qed.


Lemma max_le_l : forall m n : nat, max m n = m -> n <= m.
double induction m n.
auto.
simpl in |- *.
intros n0 H H1.
rewrite H1; trivial.
auto with arith.
auto with arith.
Qed.


Lemma max_le : forall x1 x2 x3 : nat, max x1 x2 <= x3 -> x1 <= x3 /\ x2 <= x3.
intros x1 x2 x3.
cut ({max x1 x2 = x1} + {max x1 x2 = x2}).
intros H0 H.
elim H0.
intro H1; split.
rewrite H1 in H; trivial.

apply le_trans with (m := x1).
apply max_le_l.
trivial.

rewrite H1 in H; trivial.

intro H1; split.
apply le_trans with (m := x2).
apply max_le_r; trivial.

rewrite H1 in H; trivial.

rewrite H1 in H; trivial.

apply max_dec.
Qed.



Lemma le_Smn_mn : forall m n : nat, S m <= n -> m <= n.
auto with arith.
Qed.




Lemma max_assoc :
 forall n1 n2 n3 : nat, max n1 (max n2 n3) = max (max n1 n2) n3.
simple induction n1; simple induction n2;
 try (intros; simpl in |- *; reflexivity).
intros.
case n3.
simpl in |- *.
reflexivity.

intro; repeat rewrite <- max_SS.
apply eq_S; apply H.
Qed.




Lemma max_0 :
 forall n1 n2 : nat, (le n1 n2) -> (le (max n1 0) n2).
 induction n1.
 intros.
   simpl in |- *.
   assumption.
 intros.
   simpl in |- *.
   assumption.
Qed.





(* reminder 
Check eq_add_S
(m,n:nat) (S m)=(S n)->m=s.

Check Le.le_S_n: 
(n,m:nat)(le (S n) (S m))->(le n m)

Check Le.le_n_S: 
(n,m:nat)(le n m)->(le (S n) (S m)).

Check Le.le_Sn_O:
(n:nat)~(le (S n) O).

*)


Lemma le_plus_s1 : forall a b c : nat, a + S b <= S c -> a + b <= c.
Proof.
  Require Import Arith.
  intros a b c.
  rewrite <- plus_n_Sm.
  apply le_S_n.
Qed.


Lemma le_plus_s2 : forall a b c : nat, S a + b <= S c -> a + b <= c.
Proof.
  intros a b c.
  rewrite plus_Snm_nSm.
  apply le_plus_s1.
Qed.




Ltac ElimBAnd H :=
  match goal with
  | H:(andb ?X1 ?X2 = true) |- _ => elim (andb_prop X1 X2 H); intro; intro
  end.

Ltac AbsurdLe :=
  match goal with
  | _:(S ?X1 <= 0) |- _ =>
      absurd (S X1 <= 0); [ apply le_Sn_O | assumption ]
  end.

Ltac LeS4 :=
  match goal with
  | Hle:(S ?X1 <= S ?X2) |- _ =>
      generalize (le_S_n X1 X2 Hle); clear Hle; intros Hle
  end.

Ltac LeS :=
  match goal with
  | Hle:(S ?X1 <= S ?X2) |- _ =>
      generalize (le_S_n X1 X2 Hle); clear Hle; intros Hle
  | Hle:(S ?X1 <= ?X2) |- _ =>
      generalize (le_Smn_mn X1 X2 Hle); clear Hle;
       intros Hle
       (*	|
       	[ H:(le (max ?1 ?2) ?3) |- ? ] -> 
       	     Generalize (max_le ?1 ?2 ?3 H);
       	     Clear H;Intros H;
       	     Elim H;
       	     Intro;Intro
       *)
  end.

Ltac MaxLe4 :=
  match goal with
  | H:(max ?X1 ?X2 <= ?X3) |- _ =>
      generalize (max_le X1 X2 X3 H); clear H; intros H; elim H; intro; intro
  end.

Ltac BAndDec :=
  match goal with
  |  |- {andb ?X1 ?X2 = true} + {andb ?X1 ?X2 = false} =>
      cut ({X1 = true} + {X1 = false});
       [ intros _H; elim _H; clear _H; intros _H; rewrite _H; clear _H;
          simpl in |- *; (left; reflexivity) || (right; reflexivity) || idtac
       | idtac ]
  end.



Lemma le_max_n : forall l m n : nat, l <= m -> m <= n -> max l m <= n.
double induction l m.
auto.

auto.

simpl in |- *; intros; AbsurdLe.

intros.
cut (max (S n0) (S n) = S (max n0 n)).
intro H3; rewrite H3.
generalize H1 H2; case n1.
intros; AbsurdLe.

intros; apply le_n_S; apply H0.
repeat LeS4; trivial.

repeat LeS4; trivial.

symmetry  in |- *.
apply max_SS.
Qed.


Lemma le_max_n2 : forall l m n : nat, l <= n -> m <= n -> max l m <= n.
double induction l m.
auto.

auto.

auto.

intros.
cut (max (S n0) (S n) = S (max n0 n));
 [ intro H3; rewrite H3 | symmetry  in |- *; apply max_SS ].
generalize H1 H2; case n1.
intros; AbsurdLe.

intros; apply le_n_S.
apply H0; repeat LeS4; auto.
Qed.

Lemma max_idem: forall m : nat, max m m = m.
induction m;auto with arith.
Qed.

Lemma max_le_L: forall n m k:nat, max n m <= k -> n<=k.
intros;assert (H1:=max_le n m k H);elim H1;auto.
Qed.

Lemma max_le_R: forall n m k:nat, max n m <= k -> m<=k.
intros;assert (H1:=max_le n m k H);elim H1;auto.
Qed.

Hint Rewrite plus_0_l plus_0_r plus_m_S le_S_S : rwNat.

Ltac redNat := repeat progress (simpl;autorewrite with rwNat).

Ltac doitNat :=
match goal with
[ H: (?d + ?b) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat_r]

end.

