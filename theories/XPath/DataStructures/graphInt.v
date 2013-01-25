
Require Export ZArith.
Require Export Bool.
Require Import zorder.
Require Import setOrder.
Require Import genSets.
Require Import Mapping.
Require Import List.

Module myOrder : CmpOrderTheory with Definition A := Zorder.A := cmpOrder
  Zorder.
Module ZSet := geneSets myOrder.

Definition NodeSet := ZSet.set.
Definition emptyNS := ZSet.empty.
Definition s_in := ZSet.s_in.
Definition single := ZSet.single.
Definition card := ZSet.card.

(*
Module M1:=(SetOrder ZSet).
Module M2:=(cmpOrder M1).
Module ZZSet:=(geneSets M2).
*)

Module M3 := SetDecidableEq ZSet.
Module M_Arcs := genMapping myOrder M3.
Module M_Order := genMapping myOrder Zequal.


Definition Arcs := M_Arcs.Mapping.
Definition NodeId := ZSet.A.
Definition Order := M_Order.Mapping.

(*
Definition Dpath :Set := (list NodeId).
*)



(*==============================================================================*)
(* 		a generic model of Directed Graphs, unlabeled arcs 		*)
(* 		(possibly cyclic)                           			*)
(*==============================================================================*)
Module Type graphSig.

Declare Module M_NNodes : MappingInt with Definition A := Z.

Definition Nodes := M_NNodes.Mapping.

(* Definition Node:=M_NNodes.B . *)
(*
Parameter Nodes:Set.
*)
Parameter Node : Set.

(* type for Directed graphs *)
Parameter DGraph : Set.


(* DGraph constructor *)
Parameter graph : Z -> Nodes -> Arcs -> Arcs -> Order -> DGraph.

(* Could be nice to abstract over "internal state", but I can't figure out *)
(* how to achieve this in a simple way *)
(*Parameter InternalState:Type.*)
(*Parameter graph: InternalState -> DGraph.*)

Definition empty : DGraph :=
  graph 0 M_NNodes.empty M_Arcs.empty M_Arcs.empty M_Order.empty.

(* hidden stuctures : see in implementation below
Parameter alloc:Z 
Parameter nodes:Nodes.
Parameter FwdArcs:Arcs.
Parameter BwdArcs:Arcs.
Parameter order:Order.
*)

Parameter g_in : DGraph -> NodeId -> bool.

Parameter get_node : DGraph -> NodeId -> option Node.

Parameter roots : DGraph -> NodeId -> NodeSet.
Parameter leaves : DGraph -> NodeId -> NodeSet.

Parameter children : DGraph -> NodeId -> NodeSet.
Parameter descendants : DGraph -> NodeId -> NodeSet.

Parameter parents : DGraph -> NodeId -> NodeSet.
Parameter ancestors : DGraph -> NodeId -> NodeSet.


Parameter add_node : DGraph -> Node -> NodeId * DGraph.
Parameter sub_node : DGraph -> NodeId -> DGraph.

Parameter add_arc : DGraph -> NodeId -> NodeId -> DGraph.
Parameter sub_arc : DGraph -> NodeId -> NodeId -> DGraph.

Parameter set_order : DGraph -> NodeId -> Z -> DGraph.
Parameter get_order : DGraph -> NodeId -> option Z.

Parameter project : DGraph -> NodeSet -> DGraph.


(*-------------------------------------------------------------------------------*)
Axiom
  g_in_sem :
    forall (g g' : DGraph) (id : NodeId) (N : Node),
    add_node g N = (id, g') -> g_in g' id = true.

Axiom
  g_in_sem2 :
    forall (g g' : DGraph) (id id' : NodeId) (N : Node),
    id <> id' -> add_node g N = (id', g') -> g_in g' id = g_in g id.

Axiom g_in_empty : forall id : NodeId, g_in empty id = false.

(*-------------------------------------------------------------------------------*)
Axiom
  get_node_sem1 :
    forall (g : DGraph) (id : NodeId),
    g_in g id = true -> exists N : Node, get_node g id = Some N.

Axiom
  get_node_sem2 :
    forall (g : DGraph) (id : NodeId),
    g_in g id = false -> get_node g id = None.

Axiom get_node_empty : forall id : NodeId, get_node empty id = None.

(*-------------------------------------------------------------------------------*)
Axiom
  roots_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (roots g id') = true ->
    parents g id = emptyNS /\
    (s_in id' (descendants g id) = true \/ id = id').
Axiom
  leaves_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (leaves g id') = true ->
    children g id = emptyNS /\ (s_in id' (ancestors g id) = true \/ id = id').


(*-------------------------------------------------------------------------------*)
Axiom
  add_sub_node :
    forall (g g' : DGraph) (N : Node) (id : NodeId),
    add_node g N = (id, g') -> sub_node g' id = g.
Axiom
  add_node_sem :
    forall (g g' : DGraph) (N : Node) (id : NodeId),
    add_node g N = (id, g') -> get_node g' id = Some N.

Axiom
  add_node_sem2 :
    forall (g g' : DGraph) (N : Node) (id id' : NodeId),
    id <> id' -> add_node g N = (id', g') -> get_node g' id = get_node g id.

Axiom
  sub_node_sem :
    forall (g g' : DGraph) (id : NodeId),
    sub_node g id = g' -> get_node g' id = None.

Axiom
  sub_node_sem1 :
    forall (g g' : DGraph) (id : NodeId),
    sub_node g id = g' -> get_order g' id = None.

Axiom
  sub_node_sem2 :
    forall (g g' : DGraph) (id : NodeId),
    sub_node g id = g' -> descendants g' id = emptyNS.

Axiom
  sub_node_sem3 :
    forall (g g' : DGraph) (id : NodeId),
    sub_node g id = g' -> ancestors g' id = emptyNS.

(*-------------------------------------------------------------------------------*)
Axiom
  add_sub_arc :
    forall (g g' : DGraph) (id id' : NodeId),
    add_arc g id id' = g' -> sub_arc g' id id' = g.
Axiom
  add_arc_sem1 :
    forall (g g' : DGraph) (id id' : NodeId),
    add_arc g id id = g' -> s_in id' (children g' id) = true.


(*-------------------------------------------------------------------------------*)
Axiom
  children_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (children g id') = true -> g_in g id = true.
Axiom
  descendants_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (descendants g id') = true -> g_in g id = true.

Axiom descendants_sem2 : 
        forall (g : DGraph) (x z: NodeId), 
	s_in z (descendants g x) = true -> 
        (s_in z (children g x)=true) \/
         (exists y:NodeId, 
         s_in y (children g x)=true  /\ s_in z (descendants g y)=true)
	.

Axiom
  children_descendants :
    forall (g : DGraph) (id id' : NodeId),
    s_in id' (children g id) = true -> s_in id' (descendants g id) = true.

Axiom
  descendants_closure :
    forall (g : DGraph) (id id' id'' : NodeId),
    s_in id' (descendants g id) = true ->
    s_in id'' (descendants g id') = true ->
    s_in id'' (descendants g id) = true.


(*-------------------------------------------------------------------------------*)
Axiom
  parents_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (parents g id') = true -> g_in g id = true.
Axiom
  ancestors_sem :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (ancestors g id') = true -> g_in g id = true.

Axiom
  parents_ancestors :
    forall (g : DGraph) (id id' : NodeId),
    s_in id' (parents g id) = true -> s_in id' (ancestors g id) = true.

Axiom
  ancestors_closure :
    forall (g : DGraph) (id id' id'' : NodeId),
    s_in id' (ancestors g id) = true ->
    s_in id'' (ancestors g id') = true -> s_in id'' (ancestors g id) = true.

Axiom
  children_parents :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (children g id') = true -> s_in id' (parents g id) = true.

Axiom
  parents_children :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (parents g id') = true -> s_in id' (children g id) = true.

Axiom
  descendants_ancestors :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (descendants g id') = true -> s_in id' (ancestors g id) = true.

Axiom
  ancestors_descendants :
    forall (g : DGraph) (id id' : NodeId),
    s_in id (ancestors g id') = true -> s_in id' (descendants g id) = true.

(*-------------------------------------------------------------------------------*)
Axiom
  order_sem :
    forall (g : DGraph) (id : NodeId) (z : Z),
    g_in g id = true -> get_order (set_order g id z) id = Some z.


(*-------------------------------------------------------------------------------*)
Axiom
  project_sem :
    forall (g : DGraph) (ns : NodeSet) (e : NodeId),
    s_in e ns = true ->
    g_in g e = true ->
    g_in (project g ns) e = true /\
    (forall e' : NodeId,
     s_in e' (descendants g e) = true -> g_in (project g ns) e' = true).


End graphSig.



