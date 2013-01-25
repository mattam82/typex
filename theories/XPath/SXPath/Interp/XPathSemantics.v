(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 
jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.

*********************************************************************************)
Require Import zorder.
Require Import graphInt.
Require Export xmlTree.
Require Import XPath.
Require Export XPathInduction.

(* ============================================================================= *)



Definition Tree := XTree.DGraph.
(*
Variable tree : Tree.
Hypothesis wfXml : wfXmlTree tree.
*)


(* Semantics of Axes and NodeTests *)


Definition test_node (t : Tree) (y : NodeTest) (x : NodeId) : bool :=
  match XTree.get_node t x with
  | Some node =>
      match node, y with
      | _, _node => true
      | element _, _any => true
      | attr _ _, _any => true
      | nmspace _, _any => true
      | text _, _text => true
      | element nm, name nm' => if XName.A_eq nm nm' then true else false
      | attr nm _, name nm'  => if XName.A_eq nm nm' then true else false
      | nmspace nm, name nm' => if XName.A_eq nm nm' then true else false
      | attr _ _, _attribute => true
      | element _, _element => true
      | comment _, _comment => true
      | pi _ _, _pi => true
      | _, _ => false
      end
  | None => false
  end.


Definition is_attr (t : Tree) (x : NodeId) : bool :=
  match XTree.get_node t x with
  | Some node => match node with
                 | attr _ _ => true
                 | _ => false
                 end
  | None => false
  end.


Definition is_nmspace (t : Tree) (x : NodeId) : bool :=
  match XTree.get_node t x with
  | Some node => match node with
                 | nmspace _ => true
                 | _ => false
                 end
  | None => false
  end.




(*
Definition f  (a:Axis) (x y:NodeId) (t:Tree) : Prop := 
match a with
| child =>  s_in y (XTree.children t x)=true
| descendant => s_in y (XTree.descendants t x)=true
| self => x=y
| descendant_or_self =>  x=y \/ (s_in y (XTree.descendants t x)=true)
| attribute => (s_in y (XTree.children t x)=true) /\ (is_attr t x)=true
| namespace => (s_in y (XTree.children t x)=true) /\ (is_nmspace t x)=true
end.
*)

Definition f  (a:Axis) (x:NodeId) (t:Tree) : NodeSet := 
match a with
| child =>  XTree.children t x
| descendant => XTree.descendants t x
| self => single x
| descendant_or_self =>  ZSet.union (ZSet.single x) (XTree.descendants t x)
| attribute => ZSet.filter (XTree.children t x) (is_attr t)
| namespace => ZSet.filter (XTree.children t x) (is_nmspace t)
end.





(* test wether x2 is before x1 *)
Definition order_before (t : Tree) (x1 x2 : NodeId) :=
  match XTree.get_order t x1 with
  | Some i1 =>
      match XTree.get_order t x2 with
      | Some i2 => Zlt_bool i2 i1
      | _ => false
      end
  | _ => false
  end.

(* test wether x2 is after x1 *)
Definition order_after (t : Tree) (x1 x2 : NodeId) :=
  match XTree.get_order t x1 with
  | Some i1 =>
      match XTree.get_order t x2 with
      | Some i2 => Zlt_bool i1 i2
      | _ => false
      end
  | _ => false
  end.





Module M_Phi := genMapping myOrder M3.
Definition Phi := M_Phi.Mapping.


(* Denotational Semantics *)

Fixpoint semanS (env : Phi) (t : Tree) (p : XPath) 
 (x : NodeId) {struct p} : NodeSet :=
  match p with
  | void => emptyNS
  | top => XTree.roots t x
  | slash p1 p2 => ZSet.product (semanS env t p1 x) (semanS env t p2)
  | union p1 p2 => ZSet.union (semanS env t p1 x) (semanS env t p2 x)
  | inter p1 p2 => ZSet.inter (semanS env t p1 x) (semanS env t p2 x)
  | qualif p1 q2 => ZSet.filter (semanS env t p1 x) (semanQ env t q2)
  | step a n => ZSet.filter (f a x t) (test_node t n)
  end 
 
 with semanQ (env : Phi) (t : Tree) (q : XQualif) (x : NodeId) {struct q} :
 bool :=
  match q with
  | _true => true
  | _false => false
  | not q1 => if semanQ env t q1 x then false else true
  | and q1 q2 => if semanQ env t q1 x then semanQ env t q2 x else false
  | or q1 q2 => if semanQ env t q1 x then true else semanQ env t q2 x
  | leq p1 p2 => ZSet.incl (semanS env t p1 x) (semanS env t p2 x)
  end.



    
(* Logical Semantics *)


Fixpoint Rp (t : Tree) (p : XPath) (x y : NodeId) {struct p} : Prop :=
  match p with
  | void => False
  | top => s_in y (XTree.roots t x)=true
  | union p1 p2 => Rp t p1 x y \/ Rp t p2 x y
  | inter p1 p2 => Rp t p1 x y /\ Rp t p2 x y
  | slash p1 p2 => exists z : NodeId, Rp t p1 x z  /\  Rp t p2 z y
  | qualif p q => Rp t p x y /\ Rq t q y
  | step a n => (s_in y (f a x t))=true /\ (test_node t n y)=true
  end
 
 with Rq (t : Tree) (q : XQualif) (x : NodeId) {struct q} : Prop :=
  match q with
  | _true => True
  | _false => False
  | not q => ~ Rq t q x
  | and q1 q2 => Rq t q1 x /\ Rq t q2 x
  | or q1 q2 => Rq t q1 x \/ Rq t q2 x
  | leq p1 p2 => forall z : NodeId, Rp t p1 x z -> Rp t p2 x z
  end.


Require Import XPathGrammar. 

 Notation "'Ƥ' [ p ] ( tree , x ↝  y ) " := (Rp tree p x y) (at level 0) : Xp.
 Notation "'ǫ' [ q ] ( tree , x ) " := (Rq tree q x) (at level 0) : Xq.

(* just to check the parsing of notation*)  
 Remark AA: forall x y:NodeId,  forall tree:Tree,  Ƥ[void ] ( tree , x  ↝ y ).
Abort.

  (* Pourquoi ne pas faire un interpreteur avec une relation inductive
  ca permettrait d'utiliser constructor et inversion!!
  
  pb: il faudrait la caractériser... (terminaison)*)
