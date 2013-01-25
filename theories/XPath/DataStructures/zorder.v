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
Require Import ZArith.
Require Import Bool.

Module Zorder : ReflexiveOrder with Definition A := Z.

Definition A := Z.
Definition A_le := Zle_bool.

(* properties *)
Definition reflexive := Zle_bool_refl.

Axiom dec : forall x y : A, {A_le x y = true} + {A_le x y = false}.
Axiom
  transitive :
    forall (b : bool) (x y z : A),
    A_le x y = b -> A_le y z = b -> A_le x z = b.
(*Definition transitive:Prop:=Zle_bool_trans.*)

Axiom
  antisymmetric : forall x y : A, A_le x y = true -> A_le y x = true -> x = y.
Axiom asymmetric : forall x y : A, A_le x y = false -> A_le y x = true.


End Zorder.

Module M := cmpOrder Zorder.

Module Zequal : DecidableEquality with Definition A := M.A.

Definition A := M.A.
Definition A_eq := M.eq.

(* properties *)
Definition reflexive := M.eq_reflexive.
Definition symmetric := M.eq_symmetric.
Definition eq_struct := M.eq_eq.
Definition transitive := M.eq_trans.
Definition dec := M.eq_dec. 

End Zequal.