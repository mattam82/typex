(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import ZArith.
Require Export xnodes.
Require Import xmlTree.

Section XPath.


Inductive NodeTest : Set :=
  | name : XName.A -> NodeTest
  | _any : NodeTest
  | _node : NodeTest
  | _element : NodeTest
  | _attribute : NodeTest
  | _comment : NodeTest
  | _text : NodeTest
  | _pi : NodeTest.

Inductive Axis : Set :=
  | self : Axis
  | attribute : Axis
  | namespace : Axis
  | child : Axis
  | following_sibling : Axis
  | descendant : Axis
  | descendant_or_self : Axis
  | parent : Axis
  | preceding_sibling : Axis
  | ancestor : Axis
  | ancestor_or_self : Axis.

(* ------------------------------------------------------- *)


Inductive XPath : Set :=
  | void : XPath
  | top : XPath
  | union : XPath -> XPath -> XPath
  | inter : XPath -> XPath -> XPath
  | slash : XPath -> XPath -> XPath
  | qualif : XPath -> XQualif -> XPath
  | step : Axis -> NodeTest -> XPath
with XQualif : Set :=
  | not : XQualif -> XQualif
  | and : XQualif -> XQualif -> XQualif
  | or : XQualif -> XQualif -> XQualif
  | leq : XPath -> XPath -> XQualif
  | _true : XQualif
  | _false : XQualif 
.

(*======================================== syntactic sugar =========================== *)

Definition path (p : XPath) : XQualif := not (leq p void).
Definition att (nt : NodeTest) : XPath := step attribute nt.

(* define the // notation *)
Definition slash2 (p1 p2 : XPath) :=
  union (slash p1 (slash (step descendant _node) p2)) (slash p1 p2).

(* . *)
Definition dot : XPath := step self _node.

Definition star : XPath := step child _any.

(*======================================== syntactic sugar =========================== *)


(* a small example child::PARA/descendant::*[child::*] *)
Variable PARA : XName.A.

Definition example : XPath :=
  slash (step child (name PARA))
    (qualif (step descendant _any) (path (step child _any))).

Print example.

End XPath.

Require Import Bool.

Definition axis_le (a1 a2 : Axis) : Prop :=
  match a1, a2 with
  | self, self => True
  | self, descendant_or_self => True
  | child, child => True
  | child, descendant => True
  | child, descendant_or_self => True
  | descendant, descendant => True
  | descendant, descendant_or_self => True
  | descendant_or_self, descendant_or_self => True
  | attribute, attribute => True
  | namespace, namespace => True
  | _, _ => False
  end.
  

 Lemma axis_le_transitive:  forall (a1 a2 a3: Axis), axis_le a1 a2 -> axis_le a2 a3 -> axis_le a1 a3.
 Proof.
  intros a1 a2 a3.
  case a1.
  case a2.
  case a3.
  (* 16 subgoals... *)
  Abort.

 Lemma axis_le_transitive:  forall (a1 a2 a3: Axis), axis_le a1 a2 -> axis_le a2 a3 -> axis_le a1 a3.
 Proof.
  intros a1 a2 a3.
  case a1; case a2;case a3.
  (* 216 subgoals... *)
 Abort.

  
 Lemma axis_le_transitive:  forall (a1 a2 a3: Axis), axis_le a1 a2 -> axis_le a2 a3 -> axis_le a1 a3.
 Proof.
  intros a1 a2 a3;case a1; case a2; case a3; simpl; intros; contradiction || trivial.
 Qed.
  

Definition axis_eq (a1 a2 : Axis) : bool :=
  match a1, a2 with
  | self, self => true
  | child, child => true
  | descendant, descendant => true
  | descendant_or_self, descendant_or_self => true
  | attribute, attribute => true
  | namespace, namespace => true
  | _, _ => false
  end.


Lemma axis_eq_reflexive : forall a : Axis, axis_eq a a = true.
intro a; case a; repeat trivial.
Qed.

Lemma axis_eq_symm :
 forall a1 a2 : Axis, axis_eq a1 a2 = true -> axis_eq a2 a1 = true -> a1 = a2.

intros a1 a2; case a1; case a2; simpl in |- *; intros; discriminate || auto.
Qed.

Lemma axis_eq_struct : forall a1 a2 : Axis, axis_eq a1 a2 = true -> a1 = a2.
intros a1 a2; case a1; case a2; simpl in |- *; intros; discriminate || auto.
Qed.


Lemma axis_dec :
 forall a1 a2 : Axis, {axis_eq a1 a2 = true} + {axis_eq a1 a2 = false}.
intros a1 a2.
case a1; case a2; simpl in |- *;
 (left; reflexivity) || (right; reflexivity) || idtac.
Qed.
 

(* Keep the axis in parameters for future refinment of XPath *)
Definition ntest_le (a : Axis) (n1 n2 : NodeTest) : Prop :=
  match n1, n2 with
  | _, _node => True
  | name n1, name n2 => n1 = n2
  | name n1, _any => True
  | _any, _any => True
  | _element, _element => True
  | _element, _any => True
  | _attribute, _attribute => True
  | _attribute, _any => True
  | _comment, _comment => True
  | _text, _text => True
  | _pi, _pi => True
  | _, _ => False
  end.

Definition ntest_eq (n1 n2 : NodeTest) : bool :=
  match n1, n2 with
  | name n1, name n2 => XName.A_eq n1 n2
  | _any, _any => true
  | _node, _node => true
  | _element, _element => true
  | _attribute, _attribute => true
  | _comment, _comment => true
  | _text, _text => true
  | _pi, _pi => true
  | _, _ => false
  end.

Lemma ntest_eq_reflexive : forall nt : NodeTest, ntest_eq nt nt = true.
intro nt; case nt;
 [ simpl in |- *; exact XName.reflexive
 | trivial
 | trivial
 | trivial
 | trivial
 | trivial
 | trivial
 | trivial ].
Qed.

Lemma ntest_eq_struct :
 forall n1 n2 : NodeTest, ntest_eq n1 n2 = true -> n1 = n2.

intros n1 n2; case n1; case n2; simpl in |- *; intros; discriminate || auto.
rewrite (XName.eq_struct a0 a); [ trivial | trivial ].
Qed.

Lemma ntest_eq_symm :
 forall n1 n2 : NodeTest,
 ntest_eq n1 n2 = true -> ntest_eq n2 n1 = true -> n1 = n2.

intros; apply ntest_eq_struct; trivial.
Qed.


Lemma ntest_dec :
 forall n1 n2 : NodeTest, {ntest_eq n1 n2 = true} + {ntest_eq n1 n2 = false}.
intros n1 n2.
case n1; case n2; simpl in |- *;
 (left; reflexivity) || (right; reflexivity) || idtac.
intros; apply XName.dec.
Qed.


Ltac M H :=
  match goal with
  | H:(andb ?X1 ?X2 = true) |- _ =>
      assert (_H := andb_prop X1 X2 H); elim _H; clear _H; auto
  end.



Fixpoint XPeq (p1 p2 : XPath) {struct p2} : bool :=
  match p1, p2 with
  | void, void => true
  | top, top => true
  | union p11 p12, union p21 p22 => andb (XPeq p11 p21) (XPeq p12 p22)
  | inter p11 p12, inter p21 p22 => andb (XPeq p11 p21) (XPeq p12 p22)
  | slash p11 p12, slash p21 p22 => andb (XPeq p11 p21) (XPeq p12 p22)
  | qualif p11 q12, qualif p21 q22 => andb (XPeq p11 p21) (XQeq q12 q22)
  | step a1 t1, step a2 t2 => andb (axis_eq a1 a2) (ntest_eq t1 t2)
  | _, _ => false
  end
 
 with XQeq (q1 q2 : XQualif) {struct q2} : bool :=
  match q1, q2 with
  | not q11, not q21 => XQeq q11 q21
  | and q11 q12, and q21 q22 => andb (XQeq q11 q21) (XQeq q12 q22)
  | or q11 q12, or q21 q22 => andb (XQeq q11 q21) (XQeq q12 q22)
  | leq p11 p12, leq p21 p22 => andb (XPeq p11 p21) (XPeq p12 p22)
  | _true, _true => true
  | _false, _false => true
  | _, _ => false
  end.	


Fixpoint tail (p : XPath) : XPath :=
  match p with
  | slash p1 p2 => tail p2
  | qualif p q => tail p
  | union p1 p2 => union (tail p1) (tail p2)
  | inter p1 p2 => inter (tail p1) (tail p2)
  | _ => p
  end.

Fixpoint head (p : XPath) : XPath :=
  match p with
  | slash p1 p2 => head p1
  | qualif p q => head p
  | union p1 p2 => union (head p1) (head p2)
  | inter p1 p2 => inter (head p1) (head p2)
  | _ => p
  end.
  


