(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Export zorder.
Require Export xnodes.

Require Export Mapping.
Require Export graphInt.
Require Export dgraph.

Require Import graphProp.



Module XTree
  (*	: graphSig with Definition Node := theXNode *)
  := Dgraph XNodes.

Module P := GProp XTree.

Inductive wfXmlTree (t : XTree.DGraph) : Prop :=
    wfxml :
      (* it is indeed a tree, not a general graph *)
      P.Tree t ->
      forall (e e' e'' : NodeId) (aNode : XTree.Node),
      XTree.get_node t e = Some aNode -> 
      
      (* nodes are totally ordered *)
      XTree.get_order t e <> None ->
      
      (* nodes are strictly ordered *)
      (forall z z' : Z,
       z <> z' ->
       XTree.get_order t e = Some z ->
       XTree.get_order t e' = Some z' -> (z < z')%Z \/ (z' < z)%Z) ->
      
      (* some topological properties w.r.t. node types *)
      match aNode with
      | root =>
          XTree.parents t e = emptyNS /\ XTree.children t e = single e''
      | element _ => True
      | _ => XTree.children t e = emptyNS
      end -> wfXmlTree t.