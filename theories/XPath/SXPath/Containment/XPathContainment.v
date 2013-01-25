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
Require Export XPathInduction.
(* Require XPathRewritings. *)
(* Require Export XPathGrammar. *)
Require Import graphInt.
Require Import graphProp.
(* Require mesure. *)


Require Export XPathGrammar. 

Lemma le_union :
 forall p p1 p2 : XPath,
 Ple p (union p1 p2) -> Ple p p1 \/ Ple p p2.
Abort.

       
Theorem pathSup : forall p : XPath, Ple p (union top (slash2 top star)).
Abort.
			    
			   
