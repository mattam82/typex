(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Export XPath.
Require Export XPathSemantics.
Require Export XPCAxioms.
Require Import XPCdecide.

Section demo.
Variable a : XPath.
Variable b : Name.

(* Equivalence Rule *)
Axiom slash_associatif: forall p1 p2 p3 : XPath, slash p1 (slash p2 p3) = slash (slash p1 p2) p3.


(* Tactical *)
(* Ltac solve_Ple10:= *)
(*   match goal with *)
(*   |-  (Ple (slash dot (slash star (step child (name b))))  (slash dot (step descendant (name b)))) *)
(*  => rewrite slash_associatif; *)
(*     apply g1; [ apply d1;constructor;simpl;auto *)
(*  	      | apply d2;[ apply Ple_reflexive  *)
(*  	      		 | unfold star;apply d1; constructor;simpl; auto] *)
(*  	      ] *)
(* end. *)


(* Automated Proof of ./*/b <= ./descendant::b  *)
Goal (Ple (slash dot (slash star (step child (name b))))  (slash dot (step descendant (name b)))).
rewrite !slash_associatif.
solve_Le idtac.
Qed.





























(* Proof of ./*/b <= ./descendant::b without the tactical... *)
Goal (Ple (slash dot (slash star (step child (name b))))  (slash dot (step descendant (name b)))).
rewrite slash_associatif.
apply g1.
 apply d1.
  constructor.
  simpl; auto.
 apply d2.
  apply Ple_reflexive.
  unfold star.
    apply d1.
   constructor.
   simpl; auto.
Qed.


End demo.