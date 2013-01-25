(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import Bool.
Require Import ZArith.
Require Import List.
Require Import setOrder.
Require Import Mapping.
Require Import graphInt.

Module Dgraph (M_Nodes: DecidableEquality) <: graphSig.

Module M_NNodes := genMapping myOrder M_Nodes.
Definition Nodes := M_NNodes.Mapping.
Definition Node := M_Nodes.A.
(*
Definition InternalState:Type :=
	Z -> Nodes -> Arcs -> Arcs -> Order.
*)
Inductive Graph : Set :=
    c_graph :
      forall (alloc : Z) (nodes : Nodes) (FwdArcs BwdArcs : Arcs)
        (order : Order), Graph.
Definition DGraph : Set := Graph.
Definition graph := c_graph.

Definition empty : DGraph :=
  graph 0 M_NNodes.empty M_Arcs.empty M_Arcs.empty M_Order.empty.

Definition g_in (g : DGraph) (id : NodeId) : bool :=
  match g with
  | c_graph alloc nodes fwd bwd order => M_NNodes.map_in id nodes
  end.

Definition get_node (g : DGraph) (id : NodeId) : option Node :=
  match g with
  | c_graph alloc nodes fwd bwd order => M_NNodes.map_get id nodes
  end.

Definition children (g : DGraph) (x : NodeId) : NodeSet :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      match M_Arcs.map_get x fwd with
      | None => emptyNS
      | Some s => s
      end
  end.
	
Fixpoint closure (ns : NodeSet) (g : DGraph)
 (f : DGraph -> NodeId -> NodeSet) {struct ns} : NodeSet :=
  match ns with
  | ZSet.empty => emptyNS
  | ZSet.item x ns2 => ZSet.add x (ZSet.union (f g x) (closure ns2 g f))
  end.

Definition descendants (g : DGraph) (x : NodeId) : NodeSet :=
  closure (single x) g children.

Definition parents (g : DGraph) (x : NodeId) : NodeSet :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      match M_Arcs.map_get x bwd with
      | None => emptyNS
      | Some s => s
      end
  end.
	
Definition ancestors (g : DGraph) (x : NodeId) : NodeSet :=
  closure (single x) g parents.

Definition roots (g : DGraph) (x : NodeId) : NodeSet :=
  ZSet.filter (ZSet.add x (ancestors g x))
    (fun y : NodeId =>
     match parents g y with
     | ZSet.empty => true
     | _ => false
     end).

Definition leaves (g : DGraph) (x : NodeId) : NodeSet :=
  ZSet.filter (ZSet.add x (descendants g x))
    (fun y : NodeId =>
     match children g y with
     | ZSet.empty => true
     | _ => false
     end).


Definition add_node (g : DGraph) (x : Node) : NodeId * DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      (alloc,
      graph (alloc + 1) (M_NNodes.map_add (alloc, x) nodes) fwd bwd order)
  end.

Definition add_arc (g : DGraph) (id1 id2 : NodeId) : DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      if andb (M_NNodes.map_in id1 nodes) (M_NNodes.map_in id2 nodes)
      then
       graph alloc nodes
         (M_Arcs.map_add
            (id1,
            match M_Arcs.map_get id1 fwd with
            | Some ns => ZSet.add id2 ns
            | None => single id2
            end) fwd)
         (M_Arcs.map_add
            (id2,
            match M_Arcs.map_get id2 bwd with
            | Some ns => ZSet.add id1 ns
            | None => single id1
            end) fwd) order
      (* specified arcs are inconsistent: not in known nodes *)
      else g
  end.

Definition sub_arc (g : DGraph) (id1 id2 : NodeId) : DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      if andb (M_NNodes.map_in id1 nodes) (M_NNodes.map_in id2 nodes)
      then
       graph alloc nodes
         match M_Arcs.map_get id1 fwd with
         | Some ns => M_Arcs.map_add (id1, ZSet.sub id2 ns) fwd
         | None => fwd
         end
         match M_Arcs.map_get id2 bwd with
         | Some ns => M_Arcs.map_add (id2, ZSet.sub id1 ns) bwd
         | None => bwd
         end order
      (* specified arcs are inconsistent: not in known nodes *)
      else g
  end.

Definition sub_node (g : DGraph) (id : NodeId) : DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      if M_NNodes.map_in id nodes
      then
       let f := fun (gg : DGraph) (x : NodeId) => sub_arc gg x id in
       let g1 := ZSet.reduce DGraph f g (parents g id) in
       let g2 := ZSet.reduce DGraph f g1 (children g id) in
       match g2 with
       | c_graph _ _ fwd2 bwd2 _ =>
           graph alloc (M_NNodes.map_sub id nodes) fwd2 bwd2
             (M_Order.map_sub id order)
       end
      else g
  end.

Definition set_order (g : DGraph) (id : NodeId) (ordvalue : Z) : DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      if M_NNodes.map_in id nodes
      then graph alloc nodes fwd bwd (M_Order.map_add (id, ordvalue) order)
      else g
  end.

Definition get_order (g : DGraph) (id : NodeId) : option Z :=
  match g with
  | c_graph alloc nodes fwd bwd order => M_Order.map_get id order
  end.


Definition project (g : DGraph) (ns : NodeSet) : DGraph :=
  match g with
  | c_graph alloc nodes fwd bwd order =>
      let anc := ZSet.product ns (ancestors g) in
      ZSet.reduce DGraph sub_node g anc
  end.


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



End Dgraph.
