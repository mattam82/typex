(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import setOrder.
Require Import Bool.

Require Import zorder.

(* we abstract over the various XML subtypes using Z equality *)
Module XName := Zequal.
Module XValues := Zequal.
Module XTarget := Zequal.
Module XInstr := Zequal.

Definition Name := XName.A.

Inductive Node : Set :=
  | element : XName.A -> Node
  | attr : XName.A -> XValues.A -> Node
  | nmspace : XName.A -> Node
  | text : XValues.A -> Node
  | comment : XValues.A -> Node
  | pi : XTarget.A -> XInstr.A -> Node
  | root : Node.

Definition theXNode : Set := Node.

Module XNodes <: DecidableEquality with Definition A := theXNode.


Definition A := theXNode.

Definition A_eq (n1 n2 : A) :=
  match n1, n2 with
  | element nm1, element nm2 => XName.A_eq nm1 nm2
  | attr nm1 val1, attr nm2 val2 =>
      andb (XName.A_eq nm1 nm2) (XValues.A_eq val1 val2)
  | nmspace nm1, nmspace nm2 => XName.A_eq nm1 nm2
  | text val1, text val2 => XValues.A_eq val1 val2
  | comment val1, comment val2 => XValues.A_eq val1 val2
  | pi t1 i1, pi t2 i2 => andb (XTarget.A_eq t1 t2) (XInstr.A_eq i1 i2)
  | root, root => true
  | _, _ => false
  end.

Axiom reflexive : forall x : A, A_eq x x = true.
Axiom symmetric : forall x y : A, A_eq x y = true -> A_eq y x = true.
Axiom eq_struct : forall x y : A, A_eq x y = true -> x = y.
Axiom
  transitive :
    forall x y z : A, A_eq x y = true -> A_eq y z = true -> A_eq x z = true.
Axiom dec : forall x y : A, {A_eq x y = true} + {A_eq x y = false}.

End XNodes.