(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import graphInt.
Require Import dgraph.
Require Import zorder.

Require Import Relations.

Module GProp (G: graphSig).

(*Module G := (Dgraph Zequal).*)


(*-------------------------------------------------------------------------------*)
(* some generic graph properties *)


Inductive Id (g : G.DGraph) (x : NodeId) : Prop :=
    is_id : G.g_in g x = true -> Id g x.




(* -------------------- Pathes definitions ----------------------- *)

Inductive Dpath : Set :=
  | bpath : NodeId -> NodeId -> Dpath
  | mpath : NodeId -> Dpath -> Dpath.

(* nodes just have to be adjacent, no orientation is required *)
Inductive Adjacent (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    adj :
      ZSet.s_in x1 (G.children g x2) = true \/
      ZSet.s_in x2 (G.children g x1) = true -> Adjacent g x1 x2.


Fixpoint AdjPath (g : G.DGraph) (path : Dpath) {struct path} : Prop :=
  match path with
  | bpath x1 x2 => Adjacent g x2 x1
  | mpath x p =>
      match p with
      | bpath x1 x2 => Adjacent g x1 x /\ Adjacent g x2 x1
      | mpath x1 p2 => Adjacent g x1 x /\ AdjPath g p
      end
  end.


Fixpoint Path (g : G.DGraph) (path : Dpath) {struct path} : Prop :=
  match path with
  | bpath x1 x2 => ZSet.s_in x2 (G.children g x1) = true
  | mpath x p =>
      match p with
      | bpath x1 x2 =>
          ZSet.s_in x1 (G.children g x) = true /\
          ZSet.s_in x2 (G.children g x1) = true
      | mpath x1 p2 => ZSet.s_in x1 (G.children g x) = true /\ Path g p
      end
  end.

(* A directed path is also an adjacent path *)
Axiom
  Path_AdjPath : forall (g : G.DGraph) (p : Dpath), Path g p -> AdjPath g p.


Definition From (path : Dpath) : NodeId :=
  match path with
  | bpath x x' => x
  | mpath x pp => x
  end.

Fixpoint To (path : Dpath) : NodeId :=
  match path with
  | bpath x1 x2 => x2
  | mpath x1 pp => To pp
  end.

Fixpoint In (x : NodeId) (path : Dpath) {struct path} : Prop :=
  match path with
  | bpath x1 x2 => x = x1 \/ x = x2
  | mpath x1 pp => x = x1 \/ In x pp
  end.

Inductive Nested (x : NodeId) (p : Dpath) : Prop :=
    nested : x <> From p /\ In x p /\ x <> To p -> Nested x p.

Fixpoint Join (p1 p2 : Dpath) {struct p1} : Dpath :=
  match p1 with
  | bpath x1 _ => mpath x1 p2
  | mpath x1 pp => mpath x1 (Join pp p2)
  end.


Inductive ConnectedPath (g : G.DGraph) (p1 p2 : Dpath) : Prop :=
    pconn :
      Path g p1 -> Path g p2 -> To p1 = From p2 -> ConnectedPath g p1 p2.



Inductive Link (g : G.DGraph) (p : Dpath) (x1 x2 : NodeId) : Prop :=
    link : Path g p -> From p = x1 -> To p = x2 -> Link g p x1 x2.

Fixpoint Length (path : Dpath) : Z :=
  match path with
  | bpath x1 x2 => 1%Z
  | mpath x1 pp => (1 + Length pp)%Z
  end.

Axiom PathLengthInf : forall p : Dpath, (1 <= Length p)%Z.


(* -------------------- Relation definitions ----------------------- *)


Inductive Child (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    child : Path g (bpath x2 x1) -> Child g x1 x2.

Inductive Parent (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    parent : Path g (bpath x1 x2) -> Parent g x1 x2.

Inductive Descendant (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    descendant : (exists p : Dpath, Link g p x2 x1) -> Descendant g x1 x2.

Inductive Ancestor (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    ancestor : (exists p : Dpath, Link g p x1 x2) -> Ancestor g x1 x2.

Inductive Root (g : G.DGraph) (x : NodeId) : Prop :=
    root : forall x' : NodeId, ~ Ancestor g x' x -> Root g x.

Inductive Brother (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    brother :
      forall x : NodeId, Parent g x x1 -> Parent g x x2 -> Brother g x1 x2.


Inductive Dominates (g : G.DGraph) (x1 x2 : NodeId) : Prop :=
    domin :
      (forall x : NodeId,
       Root g x -> forall p : Dpath, Link g p x x2 -> In x1 p) ->
      Dominates g x1 x2.



(* ------------------------ Properties ----------------------- *)

	
(* this is a weak connectivity: no partitions *)
Inductive Connected (g : G.DGraph) : Prop :=
    is_connected :
      (forall x1 x2 : NodeId,
       exists p : Dpath, AdjPath g p /\ From p = x1 /\ To p = x2) ->
      Connected g.


Inductive StronglyConnected (g : G.DGraph) : Prop :=
    is_sconnected :
      (forall x1 x2 : NodeId, exists p : Dpath, Link g p x1 x2) ->
      StronglyConnected g.


Inductive Cyclic (g : G.DGraph) : Prop :=
    is_cyclic : (exists e : NodeId, Id g e -> Descendant g e e) -> Cyclic g.

Inductive Dag (g : G.DGraph) : Prop :=
    is_dag : (forall e : NodeId, Id g e -> ~ Descendant g e e) -> Dag g.

(* only one input arc ("left", i.e. incoming  arc) *)
Inductive LLinear (g : G.DGraph) : Prop :=
    l_linear :
      (forall e : NodeId,
       Id g e ->
       G.parents g e = emptyNS \/
       (exists e' : NodeId, G.parents g e = single e')) -> 
      LLinear g.

(* only one output arc ("right", i.e. outgoing  arc) *)
Inductive RLinear (g : G.DGraph) : Prop :=
    r_linear :
      (forall e : NodeId,
       Id g e ->
       G.children g e = emptyNS \/
       (exists e' : NodeId, G.children g e = single e')) -> 
      RLinear g.

Inductive Tree (g : G.DGraph) : Prop :=
    is_tree : Connected g -> Dag g -> LLinear g -> Tree g.

(* note that forests cannot be connected, as defined above *)
(* It exactly means that all partitions are trees *)	
Inductive Forest (g : G.DGraph) : Prop :=
    is_forest :
      (forall e : NodeId,
       Root g e -> Tree (G.project g (ZSet.add e (G.descendants g e)))) ->
      Forest g.


Section LemUtils.

Variable g : G.DGraph.

Lemma Brother_comm :
 forall x1 x2 : NodeId, Brother g x1 x2 -> Brother g x2 x1.
intros x1 x2 H; elim H; intros x H1 H2.
constructor 1 with (x := x).
auto.
auto.
Qed.


Lemma Dec_Anc : forall x1 x2 : NodeId, Descendant g x1 x2 -> Ancestor g x2 x1.

intros x1 x2 H.
constructor; elim H; trivial.
Qed.

Lemma Anc_Dec : forall x1 x2 : NodeId, Ancestor g x1 x2 -> Descendant g x2 x1.

intros x1 x2 H.
constructor; elim H; trivial.
Qed.

Lemma Child_Parent : forall x1 x2 : NodeId, Child g x1 x2 -> Parent g x2 x1.

intros x1 x2 H.
constructor; elim H; trivial.
Qed.

Lemma Parent_Child : forall x1 x2 : NodeId, Parent g x1 x2 -> Child g x2 x1.

intros x1 x2 H.
constructor; elim H; trivial.
Qed.

Lemma mpath_elim :
 forall (p : Dpath) (x : NodeId), Path g (mpath x p) -> Path g p.
intros p x.
case p.
simpl in |- *; intros n n0 H; elim H; auto.
simpl in |- *; intros n n0 H; elim H; auto.
Qed.


Lemma Child_elim :
 forall x1 x2 : NodeId,
 Child g x1 x2 -> ZSet.s_in x1 (G.children g x2) = true.
intros x1 x2 H; elim H.
simpl in |- *; trivial.
Qed.

Lemma Parent_elim :
 forall x1 x2 : NodeId,
 Parent g x1 x2 -> ZSet.s_in x2 (G.children g x1) = true.
intros x1 x2 H; elim H.
simpl in |- *; trivial.
Qed.


Lemma Path_Path :
 forall (p : Dpath) (x : NodeId), Path g (mpath x p) -> Path g p.
simple induction p.
simpl in |- *.
intros n n0 x H; elim H; auto.

intros n d Hind.
intro x.
simpl in |- *.
intro H; elim H.
intro H1; case d.
auto.

auto.
Qed.

Lemma To_In : forall p : Dpath, Path g p -> In (To p) p.
Proof.
simple induction p.
simpl in |- *.
intros; right; trivial.

intros n d Hind H.
simpl in |- *.
right.
apply Hind.
apply Path_Path with (x := n).
exact H.
Qed.


Lemma Child_child :
 forall x1 x2 : NodeId,
 Child g x1 x2 -> ZSet.s_in x1 (G.children g x2) = true.
intros x1 x2 H; elim H.
simpl in |- *; trivial.
Qed.



Lemma mpath_intro :
 forall (x : NodeId) (p : Dpath),
 Path g p -> Child g (From p) x -> Path g (mpath x p).
intros.
elim H0.
intro H1.
simpl in H1.
simpl in |- *.
generalize H.
generalize H0.
case p.
simpl in |- *.
intros; split.
apply Child_child; trivial.

trivial.

simpl in |- *.
intros; split.
apply Child_child; trivial.

trivial.
Qed.

Lemma Path_Child :
 forall (p : Dpath) (x y : NodeId),
 Path g (mpath x p) -> y = From p -> Child g y x.
intros p x y.
case p.
simpl in |- *.
intros n n0 H H1; elim H; rewrite H1.
intros H2 H3.
constructor.
unfold Path in |- *.
trivial.

intros n d.
simpl in |- *.
intros H H1; elim H; intros H2 H3; rewrite H1.
constructor; simpl in |- *.
exact H2.
Qed.

Lemma Join_mpath :
 forall (x : NodeId) (p1 p2 : Dpath),
 Join (mpath x p1) p2 = mpath x (Join p1 p2).
auto.
Qed.

Lemma Join_bpath :
 forall (x1 x2 : NodeId) (p2 : Dpath), Join (bpath x1 x2) p2 = mpath x1 p2.
auto.
Qed.

Lemma To_To : forall (x : NodeId) (p : Dpath), To (mpath x p) = To p.
auto.
Qed.

Lemma Conn_mpath :
 forall (x : NodeId) (p1 p2 : Dpath),
 ConnectedPath g (mpath x p1) p2 -> ConnectedPath g p1 p2.
intros.
elim H.
intros.
constructor.
apply Path_Path with (x := x).
trivial.

trivial.

rewrite To_To in H2.
exact H2.
Qed.

Lemma From_Join : forall p1 p2 : Dpath, From (Join p1 p2) = From p1.
intros p1 p2; case p1.
auto.
auto.
Qed.


Lemma To_Join : forall p1 p2 : Dpath, To (Join p1 p2) = To p2.
simple induction p1; simple induction p2.
simpl in |- *.
auto.

simpl in |- *.
auto.

simpl in |- *.
intros n0 n1.
cut (n1 = To (bpath n0 n1)).
intro H1; rewrite H1; apply H.

auto.

simpl in |- *.
intros n0 d0 H1.
cut (To d0 = To (mpath n0 d0)).
intro H2; rewrite H2; apply H.

auto.
Qed.



Lemma Path_Join :
 forall p1 p2 p : Dpath, ConnectedPath g p1 p2 -> p = Join p1 p2 -> Path g p.
simple induction p1.
simpl in |- *.
intros.
elim H.
simpl in |- *.
intros.
rewrite H0.
apply mpath_intro.
elim H.
auto.

elim H.
intros.
constructor.
rewrite H3 in H4; exact H4.

intros n d Hind p2 p H1 H2.
rewrite Join_mpath in H2.
rewrite H2.
apply mpath_intro.
apply Hind with (p2 := p2).
apply Conn_mpath with (x := n).
assumption.

reflexivity.

elim H1.
intros H3 H4 H5.
generalize H3.
case d.
simpl in |- *.
intros n0 n1 H; elim H; intros H6 H7.
constructor.
simpl in |- *.
exact H6.

simpl in |- *.
intros n0 d0 H; elim H; intros H6 H7.
constructor; simpl in |- *.
exact H6.
Qed.


Lemma Path_Link :
 forall p1 p2 : Dpath,
 ConnectedPath g p1 p2 ->
 forall p : Dpath, p = Join p1 p2 -> Link g p (From p1) (To p2).
intros.
constructor.
apply Path_Join with (p1 := p1) (p2 := p2).
auto.

auto.

rewrite H0; apply From_Join; auto.

rewrite H0; apply To_Join; auto.
Qed.



Lemma Anc_Trans : transitive NodeId (Ancestor g).
unfold transitive in |- *.
intros x y z H1 H2.
constructor.
elim H1.
elim H2.
intros HH1 HH2.
elim HH1.
intro P1.
elim HH2; intro P2.
intros H3 H4.
split with (Join P2 P1).
constructor.
apply Path_Join with (p1 := P2) (p2 := P1).
constructor.
elim H3.
trivial.

elim H4; trivial.

elim H3.
elim H4.
intros.
rewrite H0; rewrite H8; reflexivity.

trivial.

rewrite From_Join; elim H3; auto.

rewrite To_Join; elim H4; auto.
Qed.



Lemma Dec_Trans : transitive NodeId (Descendant g).
unfold transitive in |- *.
intros x y z.
intros H1 H2.
apply Anc_Dec.
cut (Ancestor g z y); cut (Ancestor g y x).
intros; apply Anc_Trans with (y := y); auto.

apply Dec_Anc; auto.

intro; apply Dec_Anc; auto.

apply Dec_Anc; auto.
Qed.


Lemma Join_Path1 :
 forall p1 p2 : Dpath, Path g (Join p1 p2) -> To p1 = From p2 -> Path g p1.
simple induction p1; simple induction p2.
simpl in |- *.
intros n1 n2 H; elim H; intros H1 H2 H3; rewrite H3; trivial.

simpl in |- *.
intros.
rewrite H1; elim H0; trivial.

intros.
apply mpath_intro.
apply H with (p2 := bpath n0 n1).
rewrite Join_mpath in H0.
exact (Path_Path (Join d (bpath n0 n1)) n H0).

rewrite To_To in H1.
exact H1.

rewrite Join_mpath in H0.
apply Path_Child with (p := Join d (bpath n0 n1)).
exact H0.

apply sym_eq.
apply From_Join.

intros n0 d0 Hind H1 H2.
apply mpath_intro.
apply (H (mpath n0 d0)).
rewrite Join_mpath in H1.
exact (Path_Path (Join d (mpath n0 d0)) n H1).

rewrite To_To in H2.
exact H2.

apply Path_Child with (p := Join d (mpath n0 d0)).
rewrite Join_mpath in H1.
exact H1.

rewrite From_Join.
reflexivity.
Qed.

Lemma Join_Path2 :
 forall p1 p2 : Dpath, Path g (Join p1 p2) -> To p1 = From p2 -> Path g p2.
simple induction p1.
intros n n0 p2.
case p2.
simpl in |- *.
intros n1 n2 H; elim H; auto.

unfold Join in |- *.
intros.
exact (Path_Path (mpath n1 d) n H).

intros n d Hind p2 H1 H2.
apply (Hind p2).
rewrite Join_mpath in H1.
apply Path_Path with (x := n).
exact H1.

rewrite To_To in H2.
exact H2.
Qed.

Lemma Join_Path : forall p1 p2 : Dpath, Path g (Join p1 p2) -> Path g p2.
simple induction p1; simple induction p2.
simpl in |- *.
intros; elim H; auto.

intros n1 d H.
unfold Join in |- *.
intro H1.
apply mpath_elim with (x := n).
trivial.

intros n0 n1.
rewrite Join_mpath.
intro H1.
apply H.
apply mpath_elim with (x := n).
exact H1.

intros n0 d0 HH.
rewrite Join_mpath in HH.
rewrite Join_mpath.
intro H1.
apply H.
apply mpath_elim with (x := n).
trivial.
Qed.


Lemma CutLink :
 forall (p : Dpath) (x1 x2 x : NodeId),
 Link g p x1 x2 ->
 Nested x p ->
 forall p1 p2 : Dpath, Link g p1 x1 x -> p = Join p1 p2 -> Link g p2 x x2.
Abort.


End LemUtils.

(* to be proved *)
Axiom
  TreeRoot :
    forall g : G.DGraph,
    Tree g ->
    forall x : NodeId,
    Id g x -> exists r : NodeId, Id g r /\ G.roots g x = single r.


End GProp.