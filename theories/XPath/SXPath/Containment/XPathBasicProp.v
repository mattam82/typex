(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import XPath.
Require Import XPathInduction.
Require Import nat_basics.

(*
(* now.... go on *)
Lemma XPeq_reflexive
     : (x:XPath)(XPeq x x)=true
	.
Apply
 XJ1 with P:=[x:XPath](XPeq x x)=true P0:=[y:XQualif](XQeq y y)=true.
Auto.

Auto.

Simpl.
Exact xnodes.XName.reflexive.

Simpl.
Intros.
Rewrite -> xnodes.XName.reflexive.
Rewrite -> H.
Rewrite -> H0; Auto.

Simpl.
Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Simpl; Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Simpl; Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Simpl; Intros.
Rewrite -> axis_eq_reflexive.
Rewrite -> ntest_eq_reflexive.
Auto.

Auto.

Auto.

Simpl.
Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Simpl; Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Auto.

Auto.
Simpl; Intros.
Rewrite -> H.
Rewrite -> H0; Auto.

Auto.

Auto.

Qed.




Definition eq_prop
	:= 
	[A:Set;P:A->A->bool]
	[x1,x2:A]((P x1 x2)=true -> x1=x2)
	. 

Lemma Xeq_struct1: 
	((p1,p2:XPath)(eq_prop XPath XPeq p1 p2))
	/\ 
	((q1,q2:XQualif)(eq_prop XQualif XQeq q1 q2))
	.
Apply HGen22.
Unfold Hyp22 eq_prop.
Induction n.

(* base cases *)
Split;[
	Intros p1 p2;
	Case p1;Case p2;
	Simpl;Intros;Discriminate Orelse AbsurdLe Orelse Trivial
	|
	Intros q1 q2;
	Case q1;Case q2;
	Simpl;Intros;Discriminate Orelse AbsurdLe Orelse Trivial
	].

(* Induction step *)
Intros n0 Hi;Elim Hi;Intros Hi1 Hi2. 
Split; [ Intros p1 p2 | Intros q1 q2 ].

(*----------------------------------------- XPath cases *)
Case p1; Case p2; Simpl; Intros;Discriminate Orelse Trivial.

(* case var *)
Rewrite -> (xnodes.XName.eq_struct a0 a);[ Trivial | Trivial ].

(* for case *)
ElimBAnd H0; Rewrite -> (xnodes.XName.eq_struct a0 a).
Cut x1=x/\x2=x0.
Intro H5; Elim H5; Intros H6 H7; (Rewrite -> H6);Rewrite -> H7; Trivial.
Split; [ Apply Hi1 | Apply Hi1 ].
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.
ElimBAnd H0; Trivial.
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.
ElimBAnd H0; Trivial.
Trivial.

(* union *)
Cut x1=x/\x2=x0;
 [ Intro H3; Elim H3; Intros H4 H5; (Rewrite -> H4); Rewrite -> H5;
    Trivial
 | Split ].
Apply Hi1.
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.

ElimBAnd H0; Trivial.

Apply Hi1.
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.

ElimBAnd H0; Trivial.

(* slash *)
Cut x1=x/\x2=x0;
 [ Intro H3; Elim H3; Intros H4 H5; Rewrite -> H4; Rewrite -> H5;
    Trivial
 | Split ].
Apply Hi1.
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.

ElimBAnd H0; Trivial.

Apply Hi1.
Apply le_max_n2; LeS4; Repeat MaxLe4; Auto.

ElimBAnd H0; Trivial.

(* qualif case *)
Cut x1=x/\x2=x0;
 [ Intro H3; Elim H3; Intros H4 H5; (Rewrite -> H4);
    Rewrite -> H5; Trivial
 | Split ].
Apply Hi1;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [Trivial | Trivial]
 | ElimBAnd H0; Trivial ].
Apply Hi2;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [Trivial | Trivial]
 | ElimBAnd H0; Trivial ].

(* step *)
ElimBAnd H0.
Rewrite -> (axis_eq_struct a0 a).
Rewrite -> (ntest_eq_struct n2 n1); Trivial.
Trivial.

(*--------------------  XQualif part *)

Case q1; Case q2; Simpl; Intros; Discriminate Orelse Auto with arith.

(* case not *)
Cut x0=x; [ Intro H1; (Rewrite -> H1); Trivial | Apply Hi2 ].
Apply le_max_n2; LeS4; MaxLe4; [ Trivial | Trivial ].
Trivial.

(* case and *)
Cut x1=x/\x2=x0;
 [ Intro H1; Elim H1; Intros H2 H3; (Rewrite -> H2); (Rewrite -> H3);
    Trivial
 | Split ].
Apply Hi2;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

Apply Hi2;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

(* case or *)
Cut x1=x/\x2=x0;
 [ Intro H1; Elim H1; Intros H2 H3; Rewrite -> H2; Rewrite -> H3;
    Trivial
 | Split ].
Apply Hi2;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

Apply Hi2;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

(* case leq *)
Cut x1=x/\x2=x0;
 [ Intro H1; Elim H1; Intros H2 H3; Rewrite -> H2; Rewrite -> H3;
    Trivial
 | Split ].
Apply Hi1;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

Apply Hi1;
 [ Apply le_max_n2; LeS4; Repeat MaxLe4; [ Trivial | Trivial ]
 | ElimBAnd H0; Trivial ].

Qed.


Lemma Xeq_struct: 
	( (p1,p2:XPath) (XPeq p1 p2)=true -> p1=p2 )
	/\ 
	( (q1,q2:XQualif)(XQeq q1 q2)=true -> q1=q2 )
	.
Proof Xeq_struct1.


Lemma XPeq_struct: 
	(p1,p2:XPath) (XPeq p1 p2)=true -> p1=p2.

Assert H:=Xeq_struct;Elim H;Intros H1 H2;Exact H1.
Qed.


Lemma XPeq_symmetric
     : (x1,x2:XPath)(XPeq x1 x2)=true -> (XPeq x2 x1)=true
	. 
Intros x1 x2 H;Rewrite (XPeq_struct x1 x2 H);Apply XPeq_reflexive.
Qed.

Lemma XPeq_transitive:
	(p1,p2,p3:XPath)
	(XPeq p1 p2)=true -> (XPeq p2 p3)=true -> (XPeq p1 p3)=true.
Intros; Cut p1=p3.
Intro H1; Rewrite -> H1; Apply XPeq_reflexive.

Transitivity p2.
Apply XPeq_struct; Trivial.

Apply XPeq_struct; Trivial.
Qed.


Lemma myFalse: (x:bool)(andb x false)=false.
Intro;Rewrite andb_sym;Simpl;Reflexivity.
Qed.



Definition dec_prop
	:= 
	[A:Set;P:A->A->bool]
	[x1,x2:A]({(P x1 x2)=true}+{(P x1 x2)=false})
	. 


Lemma Xeq_dec1:
	( (p1,p2:XPath)(dec_prop XPath XPeq p1 p2))
	*
	((q1,q2:XQualif)(dec_prop XQualif XQeq q1 q2))
	.

Apply HGen22_rec.
Unfold Hyp22_rec dec_prop.
Induction n.
Split.
Intros p1 p2; Case p1; Case p2; Simpl; Intros;
 (Left; Reflexivity) Orelse
   (Right; Reflexivity) Orelse AbsurdLe Orelse Auto.

Intros.
MaxLe4.
Generalize H0; Generalize H1; Case q1; Case q2; Simpl; Intros;
 Discriminate Orelse
   (Left; Reflexivity) Orelse
     (Right; Reflexivity) Orelse AbsurdLe Orelse Idtac.

Intros n0 Hi; Elim Hi; Intros Hi1 Hi2.
Split.
Intros p1 p2.
Case p1; Case p2; Simpl; Intros;
 Discriminate Orelse
   AbsurdLe Orelse
     (Left; Reflexivity) Orelse (Right; Reflexivity) Orelse Idtac.
Apply xnodes.XName.dec.

LeS4.
Repeat MaxLe4.
Cut {(xnodes.XName.A_eq a0 a)=true}+{(xnodes.XName.A_eq a0 a)=false}.
Intro H6.
Elim H6; Intro H7; Rewrite -> H7; Simpl.
Generalize H2 H4; Case x1; Case x; Simpl; Intros;
 AbsurdLe Orelse
   (Left; Reflexivity) Orelse (Right; Reflexivity) Orelse Idtac.
Apply Hi1; Apply le_max_n2; Auto.

Apply Hi1; Apply le_max_n2; Auto.

Cut {(xnodes.XName.A_eq a2 a1)=true}+{(xnodes.XName.A_eq a2 a1)=false};
 [ Idtac | Apply xnodes.XName.dec ].
Intro H10; Elim H10; Intro H11; Rewrite -> H11; Simpl;
 [ Apply Hi1 | Right; Trivial ].
Apply le_max_n2; Auto.

Cut {(xnodes.XName.A_eq a2 a1)=true}+{(xnodes.XName.A_eq a2 a1)=false};
 [ Intro H10; Elim H10; Intro H11; Rewrite -> H11; Simpl;
    [ Idtac | Right; Trivial ]
 | Apply xnodes.XName.dec ].
Cut {(XPeq x5 x3)=true}+{(XPeq x5 x3)=false};
 [ Intro H12; Elim H12; Intro H13; Rewrite -> H13; Simpl;
    [ Idtac | Right; Trivial ]
 | Apply Hi1 ].
Cut {(XPeq x6 x4)=true}+{(XPeq x6 x4)=false};
 [ Intro H14; Elim H14; Intro H15; Rewrite -> H15; Simpl;
    [ Idtac | Right; Trivial ]
 | Apply Hi1 ].
Apply Hi1.
Apply le_max_n2; Auto.

Apply le_max_n2; Auto.
LeS; MaxLe4; Trivial.

Repeat LeS; MaxLe4; Trivial.

Apply le_max_n2; Repeat (LeS; MaxLe4; Trivial).

BAndDec.
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi2; Apply le_max_n2; Auto.

Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Apply ntest_dec.
Apply axis_dec.

Right; Trivial.

Apply xnodes.XName.dec.

BAndDec.
Repeat (LeS; MaxLe4).
Apply Hi1; Apply le_max_n2; Auto.
Repeat (LeS; MaxLe4).
Repeat MaxLe4.
Auto.

Repeat LeS; Repeat MaxLe4; Auto.

Repeat LeS; Repeat MaxLe4; Auto.
Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat LeS; Repeat MaxLe4.
Apply Hi1; Apply le_max_n2; Auto.

Repeat LeS; Repeat MaxLe4; Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.
Repeat LeS; Repeat MaxLe4; Apply Hi1; Apply le_max_n2; Auto.

BAndDec.
Apply ntest_dec.

Apply axis_dec.

Intros q1 q2; Case q1; Case q2; Simpl; Intros;
 (Left; Reflexivity) Orelse (Right; Reflexivity) Orelse Idtac.
(* Repeat LeS; Repeat MaxLe4; Apply Hi1; Apply le_max_n2; Auto. *)
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.

BAndDec.
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.

BAndDec.
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.
Repeat LeS; Repeat MaxLe4; Apply Hi2; Apply le_max_n2; Auto.

BAndDec.
Repeat LeS; Repeat MaxLe4; Apply Hi1; Apply le_max_n2; Auto.
Repeat LeS; Repeat MaxLe4; Apply Hi1; Apply le_max_n2; Auto.
Qed.


Lemma XPeq_dec:(p1,p2:XPath) {(XPeq p1 p2)=true}+{(XPeq p1 p2)=false}.
Intros p1 p2.
Elim Xeq_dec1.
Intros H1 H2; Unfold dec_prop in H1; Auto.
Qed.


Require setOrder.

Module XPequal:DecidableEquality 
		with Definition A := XPath
		.

Definition A:= XPath .
Definition A_eq:=XPeq.

(* properties *)
Definition reflexive  := XPeq_reflexive.
Definition symmetric  := XPeq_symmetric.


Definition eq_struct  := XPeq_struct.

Definition transitive := XPeq_transitive.

Definition dec        := XPeq_dec.


End XPequal.

(* signal the end of the module compilation to the user *)
Print XPequal.
*)