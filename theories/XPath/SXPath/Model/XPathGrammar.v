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
Require Export xnodes.
(*
Require Export XPCAxioms.
Require Import Notations.
*)
(* ------------------------------------------------------
 A COQ Grammar that allows to use the usual XPath syntax
 instead of the prefixed notation. The considered XPath
 abstract syntax is the following:
 
 p ::= ^ | ! | p|p | a::N | 
      (p) | p/p | p[q]
   
 q::= true | false | (q) | not q |
      q and q | q or q | p <= p 
       
  where the symbol "^" denotes the root node and the
  symbol "!" denotes the void path.
 ------------------------------------------------------ *)

Bind Scope Xp with XPath.


Notation "p1 ⎮ p2" := (union p1 p2) (at level 85, right associativity) : Xp.
Notation "p1 ∩ p2" := (inter p1 p2) (at level 80, right associativity): Xp.
Notation "p1 '/' p2" := (slash p1 p2) (at level 40, left associativity) : Xp.
Notation "p1 '//' p2" := (slash2 p1 p2) (at level 35, right associativity): Xp.
Notation "p [ q ]" := (qualif p q)  (at level 34, left associativity) : Xp.
Notation "a ::: N" := (step a N) (at level 34, left associativity) : Xp .
Notation "⋀" := top (at level 20, no associativity) : Xp .
Notation "⊥" := void (at level 20, no associativity) : Xp .
Notation "∙" := dot (at level 20, no associativity) : Xp .
Notation "'*'" := star (at level 20, no associativity) : Xp .
Notation "@ a" := (att a) (at level 20, no associativity) : Xp .

Bind Scope Xq with XQualif.

(* conflict with bool 
Notation "'true'" := _true  : Xq.
Notation "'false'" := _false : Xq.
*)
Notation "q1 'or' q2" := (or q1 q2) (at level 85, right associativity) : Xq.
Notation "q1 'and' q2" := (and q1 q2) (at level 80, right associativity) : Xq.
Notation "'not' q" := (not q) (at level 75, no associativity) : Xq.
Notation "p1 ⊑ p2" := (leq p1 p2) (at level 70, no associativity) : Xq. 
Notation "# p" := (path p) (at level 70, no associativity) : Xq.

Bind Scope Xa with Axis.

Notation "'self'" := self  : Xa.
Notation "'attribute'" := attribute : Xa.
Notation "'namespace'" := namespace : Xa .
Notation "'child'" := child  : Xa.
Notation "'descendant'" := descendant : Xa.
Notation "'descendant-or-self'" := descendant_or_self  : Xa.

Bind Scope Xnt with NodeTest.

Notation "⋆'"            := _any : Xnt.
Notation "'%node()'"      := _node : Xnt.
Notation "'%element()'"   := _element : Xnt.
Notation "'%attribute()'" := _attribute : Xnt.
Notation "'%comment()'"   := _comment : Xnt.
Notation "'%text()'"      := _text : Xnt.
Notation "'%pi()'"        := _pi : Xnt.
Notation "'!' nm"        := (name nm) (at level 10) : Xnt. 

Open Scope Xp.

Open Scope Xq.
Open Scope Xa.
Open Scope Xnt.
