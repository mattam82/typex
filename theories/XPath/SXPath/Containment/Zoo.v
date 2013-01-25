(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)

Require Export XPCAxioms.
Require Export XPathGrammar.

(*
Remark z1 : (Ple top (step ancestor _node)).
Remark z2 : ~(Ple top (step ancestor _any)).
*)

Fact z1: forall a b c:Name, child:::!a/child:::!b/child:::!c ≤ *[#descendant:::!c]/*/* .
Admitted.

(*


Lemma z2:
    forall p1 p2:XPath
    forall a:Name,
    (Ple p1 p2) -> (Ple `~p1/a` `~p2//a`).
Intros.
SolveLe Idtac.
Qed.

Lemma z3:
    forall p1:XPath
    forall a:Name,
    ~(head p1)=top -> (Ple `~p1/a` `^/descendant::a`).
Intros.
SolveLe Idtac.
Qed.

Lemma z4:
    forall p1:XPath
    forall a:Name,
    ~(head p1)=top -> (Ple `~p1/a` `^/descendant::a`).
Intros.
SolveLe Idtac.
Qed.

Lemma z5:
    forall p1:XPath
    forall a:Name,
    ~(head p1)=top -> (Ple `~p1//a` `^//a`).
Intros.
SolveLe Idtac.
Qed.

Conjecture z6:
    forall p1:XPath
    forall a:Name
    (Peq `child::attribute()` `@*`)
    .

Conjecture z7:
    forall p1:XPath
    forall a:Name,
    (Peq
     `node()`
     `@* | * | namespace::* | comment() | processing_instruction() | text()`
     )
    .
*)

