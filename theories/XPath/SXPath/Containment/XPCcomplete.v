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
Require Export XPequiv.
Require Export XPCAxioms.
Require Export XPathInduction.
(* Require XPathRewritings. *)

Require Import graphInt.
Require Import graphProp.
(* Require mesure. *)


Require Import XPequiv.

Parameter tree : Tree.
Require Import XPathGrammar.

Notation "x '∊' t" := (XTree.g_in t x = true) (at level 0).

Lemma sem_decidable: 
    forall p:XPath, 
    exists x :NodeId,
    exists y :NodeId,
     (x∊tree) /\
     (y∊tree) /\
     ( Ƥ [p](tree, x ↝  y)  \/  ~Ƥ [p](tree, x ↝  y) )
.
induction p.
exists 0%Z;exists 0%Z;intuition.
[apply root_in_tree | split;[apply root_in_tree | right;simpl;auto]].
exists root;exists root;split;[apply root_in_tree | split;
[apply root_in_tree | left;apply rootJoinable;apply root_in_tree]].

Focus.
elim IHp1;intros x H;elim H;clear H.
intros y [x_in_tree [y_in_tree [Ha | Ha]]].
exists x;exists  y;split;trivial;split;trivial;left;simpl;left;trivial.

elim IHp2;intros w H;elim H;clear H.
intros z [w_in_tree [z_in_tree [Hb | Hb]]].
exists w;exists  z;split;trivial;split;trivial;left;simpl;right;trivial.
(* grrr.... *)
Admitted.

Conjecture sem_decidable2:
   forall p:XPath, 
   forall x y :NodeId,
     ( Ƥ [p](tree, x ↝  y)  \/  ~Ƥ [p](tree, x ↝  y) )
.

Lemma false_equiv_void:
  forall p:XPath,
  (forall x y:NodeId,
    (x∊tree) -> (y∊tree) -> ~Ƥ [p](tree, x ↝  y) ) -> (p ⇽⇾ void)
  .
induction p ;intro H.
apply Pequiv_reflexive.
Admitted.


Hint Rewrite [ plus_0_l plus_0_r plus_m_S plus_Snm_nSm le_S_S ] in rwNat.
Hint Rewrite <- [ max_SS ] in rwNat.

Ltac redNat := repeat progress (simpl;autorewrite [ rwNat]).

Ltac doitNat := simpl;
match goal with
| [ H: (_ + ?b) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat_r | apply H];try doitNat
| [ H: (_ + ?b) <= ?c  |-  ?b + _ <= ?c ] 
	=> rewrite plus_comm ;doitNat
| [ H: (?b + _) <= ?c  |-  ?b + _ <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat_l | apply H];try doitNat
| [ H: (?b + _) <= ?c  |-  _ + ?b <= ?c ] 
	=> rewrite plus_comm ; try doitNat

| [ H: (max ?a _) + (max ?b _) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat | apply H];doitNat
| [ H: (max ?a _) + (max _ ?b ) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat | apply H];doitNat
| [ H: (max _ ?a ) + (max _ ?b ) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat | apply H];doitNat
| [ H: (max _ ?a ) + (max ?b _ ) <= ?c  |-  ?a + ?b <= ?c ] 
	=> eapply le_trans;[apply plus_le_compat | apply H];doitNat

|   |-  ?a <= max ?a _ 
	=> apply le_max_l
|  |-  ?a <= max _ ?a  
	=> apply le_max_r
| [ H: (S ?a) <= ?c , H0: ?a  |-  _ <= ?c ] 
	=> auto with arith
| [ H: (S _) <= ?c  |-  _ <= ?c ] 
	=> generalize (le_Sn_le _ _ H);intro;try doitNat
| [ H: (S _) <= (S ?c)  |-  _ <= ?c ] 
	=> generalize (le_S_n _ _ H);intro;try doitNat
| _ => auto with arith
end.

(* Simplified description of Normalized terms:               *)
(* Just capture the syntactic enbedding rules                *)
(*                                                           *)
(* - No left/right associativity                             *)
(* - No partial evaluation e.g. (void|p) -> p                *)
(* - No particular constraints on basic constituents such as *)
(*      - axis homogeneity                                   *)
(*      - left most position for self, top,var               *)
(*      - unicity of self ,top                               *)
(*      - maybe others as well...                            *)
Inductive SNf: XPath-> Prop :=
| snf:
    forall p:XPath,
    (SNf_union p) ->
    (SNf p)
    
with SNf_union: XPath -> Prop :=
| snf_union:
    forall p1 p2:XPath,
    (SNf_union p1) ->
    (SNf_union p2) ->
    (SNf_union (union p1 p2))
| snf_union_other:
    forall p:XPath,
    (SNf_slash p)->
    (SNf_union p)


with SNf_slash: XPath -> Prop :=
| snf_slash:
    (* a::N[q]/p2 *)
    forall p1 p2:XPath,
    (SNf_slash p1)->
    (SNf_slash p2)->
    (SNf_slash (slash p1 p2))
| snf_slash_other:
    forall p:XPath,
    (SNf_base p)->
    (SNf_slash p)

with SNf_base: XPath -> Prop :=
| snf_void:
    (SNf_base void)
| snf_top:
    forall q:XQualif,
    (SNf_Q q) ->
    (SNf_base (qualif top q))
| snf_qualif:
    forall (q:XQualif) (a:Axis)(n:NodeTest),
    (SNf_Q q)->
    (SNf_base (qualif (step a n) q))
    
with SNf_Q : XQualif -> Prop :=
| nfq:
    forall (q:XQualif),
    (SNf_Q_and q)->
    (SNf_Q q)

with SNf_Q_and : XQualif  -> Prop :=
| nfq_and:
    forall q1 q2:XQualif,
    (SNf_Q_and q1)->
    (SNf_Q_and q2)->
    (SNf_Q_and (q1 and q2))
| nfq_and_other:
    forall (q:XQualif),
    (SNf_Q_not q)->
    (SNf_Q_and q)
with SNf_Q_not : XQualif -> Prop :=
| nfq_not:
    forall (p1 p2:XPath),
    (SNf_Q_base (leq p1 p2))->
    (SNf_Q_not (not (leq p1 p2)))
| nfq_not_other:
    forall (q:XQualif),
    (SNf_Q_base q)->
    (SNf_Q_not q)
    
with SNf_Q_base : XQualif -> Prop :=
| snfq_true:
    (SNf_Q_base _true)
.

Hypothesis nf_always: 
  forall p:XPath, 
  exists np:XPath, 
  (p ⇽⇾ np) /\  (SNf np) /\  ((CXP np)<=(CXP p))
  .

Definition Qipl_complete (q1 q2 : XQualif ) : Prop :=
  (
     forall x:NodeId,    
    (x∊tree) ->  (Rq tree q1 x  -> Rq tree q2 x)
    ) -> Qipl q1 q2
  .

Definition Ple_complete (p1 p2 : XPath) : Prop :=
  (
     forall x y:NodeId,    
    (x∊tree) ->
    (y∊tree) ->   (Rp tree p1 x y -> Rp tree p2 x y)
    ) ->  (Ple p1 p2)	
  .

Definition Pequiv_complete (p1 p2 : XPath) : Prop :=
  (
     forall x y:NodeId,    
    (x∊tree) -> 
    (y∊tree) ->  (Rp tree p1 x y <-> Rp tree p2 x y)
    ) ->  (p1 ⇽⇾ p2)	
  .

Definition Qequiv_complete  (q1 q2 : XQualif) : Prop :=
  (
    forall x:NodeId,    
    (x∊tree) ->      (Rq tree q1 x  <-> Rq tree q2 x)
    ) ->  (q1 ⇐⇒ q2)	
  .



 Require Export XPathGrammar.

Lemma completness :
 (forall p1 p2 : XPath, Ple_complete p1 p2) /\
 (forall p1 p2 : XPath, Pequiv_complete p1 p2) /\
 (forall q1 q2 : XQualif, Qipl_complete q1 q2) /\
 (forall q1 q2 : XQualif, Qequiv_complete q1 q2).

apply HGen2222plus.
(* forall n : nat, Hyp22 Ple_complete Qipl_comple n *)
induction n;unfold Hyp2222plus.

Focus 2.
 simpl in IHn;unfold Hyp2222plus in IHn;split;[idtac | split;[idtac | split]];
 elim IHn; intros IHn1 [IHn2 [IHn3 IHn4]];clear IHn.

  (* ------------------ Paths -------------------------- *)
  Focus.
    intros p1 p2; case p2. (* eight sub goals *)

Focus 3.
(* Ple_complete p1 (x ⎮ x0) *)
intros p21 p22 H;simpl in H.
unfold Ple_complete.
intro Ha.
apply p_gene_L.
assert (Nf:= (nf_always p1)).
elim Nf;intros nf [Hb [Hc Hd]].
exists nf;split.
constructor;trivial.
apply IHn1.
Focus 2.
intros;apply Ha;trivial.
Require Import XPEsound.
generalize (equiv_sound _ _ Hb).
unfold PP.
intro.
elim (H3 x y H0 H1);intros He Hf.
auto.

intros.
generalize (sem_decidable2 p1 x y).
intros [Ha | Ha].
elim (H0 Ha);intro Hb.
apply p_union_R.
apply IHn1.
generalize H;redNat;intro H1;doitNat.
intro;trivial.
apply p_gene_R.
exists (p22 ⎮ p21);split;constructor.
constructor.
apply IHn1.
generalize H;redNat;intro H1;doitNat.
intro;trivial.
assert (Hb:=(false_equiv_void p1)).

(* n= O *)
 split.
  (* Paths *)
  Focus.
  intros p1 p2;
  case p1;case p2;simpl;intros;try AbsurdLe;
  unfold Ple_complete;[
        constructor
      | constructor
| idtac
(*      | intro H1;elimtype False;exact (H1 rootNotEmpty) *)
      | intros; apply Ple_reflexive
      ].
intros.
elimtype False.
generalize (rootNotEmpty ctx).
intros.
elim H1;intros root H2.
generalize (H2 ctx_in_tree);intro H3.
apply H0 ; trivial.
rewrite (equRoot _ _ ctx_in_tree H3);exact root_in_tree.
trivial.

split.
  (* Pequiv *)
  Focus.
  intros p1 p2;
  case p1;case p2;simpl;intros;try AbsurdLe;
  unfold Pequiv_complete; try (intros;apply Pequiv_reflexive).

  intro Ha;elim (Ha ctx root ctx_in_tree root_in_tree);
  intros _ Hc;elimtype False;apply Hc;apply rootJoinable;apply ctx_in_tree.

  intro Ha;elim (Ha ctx root ctx_in_tree root_in_tree);
  intros Hc _;elimtype False;apply Hc;apply rootJoinable;apply ctx_in_tree.

split.
  (* Qualifiers *)
  Focus.
  intros q1 q2;
  case q1;case q2;simpl;intros;try AbsurdLe;unfold Qipl_complete;try constructor.
  intro H1;elimtype False.
  apply (H1 ctx ctx_in_tree);simpl;trivial.

  (* Qequiv *)
  Focus.
  intros q1 q2;
  case q1;case q2;simpl;intros;try AbsurdLe;unfold Qequiv_complete;try (intros;apply Qequiv_reflexive).
   intro Ha;elim (Ha ctx ctx_in_tree);
  intros Hc _;elimtype False;apply Hc;simpl;trivial.

   intro Ha;elim (Ha ctx ctx_in_tree);
  intros _ Hc ;elimtype False;apply Hc;simpl;trivial.

(* n= (S k) *)
 simpl in IHn;unfold Hyp2222plus in IHn;split;[idtac | split;[idtac | split]];
 elim IHn; intros IHn1 [IHn2 [IHn3 IHn4]];clear IHn.

  (* ------------------ Paths -------------------------- *)
  Focus.
    intros p1 p2; case p2. (* eight sub goals *)

Focus 3.
(* Ple_complete p1 (x ⎮ x0) *)

intros p21 p22 H;simpl in H;unfold Ple_complete;intro Hcomp.
generalize (sem_decidable p1).
intros [x [ y [ x_in_tree [ y_in_tree [Ha | Ha]] ] ] ].

elim (Hcomp _ _ x_in_tree y_in_tree Ha);intro Hb.
constructor.
apply IHn1.
generalize H;redNat;intro H0;doitNat.

Focus 7.
case p1.

Focus 3.
(* Ple_complete (x ⎮ x0) (a :: n0) *)
simpl;intros p11 p12 a N H;unfold Ple_complete;intros.
constructor.
apply IHn1.

doitNat.
intros;apply H0;trivial.
simpl;left;trivial.

apply IHn1.
doitNat.
intros;apply H0;trivial.
simpl;right;trivial.

Focus 10.
(* Ple_complete (x / x0) (a :: n0) *)
simpl;intros p11 p12 a N H;unfold Ple_complete.
case a.
intros.
constructor.

simpl.
apply


Focus 5.
case p1.
Focus 5.
intros p21 p22 H;simpl in H;unfold Ple_complete;intro Hcomp.
constructor.
constructor.
apply IHn1.

generalize H;redNat;intro H0;doitNat.

intros x y x_in_tree y_in_tree Ha.
simpl in IHp1_1;unfold Ple_complete in IHp1_1.

generalize (Hcomp x ctx x_in_tree ctx_in_tree).
simpl.
intros.

Focus 3.
(* Ple_complete p1 (x ⎮ x0) *)

intros p21 p22 H;simpl in H;unfold Ple_complete;intro Hcomp.
generalize (nf_always p1);intros [np [Ha Hb]].
apply p_gene_L.
exists np;split;trivial.
inversion Hb.
inversion H0.

induction p1.
Focus 3.
constructor.
apply IHp1_1.
generalize H;redNat;intro.
doitNat.


constructor.
apply IHn1.

    (* void p2 *)
    constructor.

Focus 4.
(* -----------------------------------------------------------*)
(* Ple_complete (x / x0) p2 *)
(* -----------------------------------------------------------*)
intros p11 p12 p2;case p2.

Focus 3.
(* Ple_complete (p11 / p12) (x ⎮ x0) *)
unfold Ple_complete.
intros p21 p22 H HCompl;simpl in H.

elim (HCompl ctx ctx ctx_in_tree ctx_in_tree Ha).

constructor.
apply IHn1.

simpl;generalize (le_S_n _ _ H);rewrite plus_m_S.
case n.
intro Ha;inversion Ha.
intros n0 Ha;apply le_n_S;generalize (le_S_n _ _ Ha);intro Hb;eapply le_trans;[ idtac | apply Hb];
apply plus_le_compat_l;auto with arith.

intros x y x_in_tree y_in_tree Ha.
elim (HCompl x y x_in_tree y_in_tree Ha).


cut ( (p11 / p12 ≤ p21) \/ (p11 / p12 ≤ p22)).
intros [Ha | Ha];[constructor;trivial | apply p_gene_R].
exists (p22 ⎮  p21);split;constructor;trivial;constructor.


(* Ple_complete (p11 / p12) (⊥) *)
unfold Ple_complete.
intros H HCompl;simpl in H.
constructor || apply p_gene_L;exists void;split;constructor.
eapply Pequiv_trans with (p2:=void/p12 ).
eapply equ_s_slash_L.

simpl in H.
simpl in HCompl.

    (* top p2 *)
    Focus.
    induction p2.
    Focus 3.
unfold Ple_complete in IHp2_1, IHp2_2 |- *.
simpl.
intros H H0.
generalize (H0 x root).
rewrite (rootOfTree x x_is_a_node).
rewrite ZSet.single_sem.
intros H1;cut (true=true);[intro H2 | reflexivity].
elim (H1 H2);intro Ha.

apply p_union_R.
apply IHp2_1.
simpl;rewrite le_S_S in H.
generalize (max_le_L _ _ _ H);auto with arith.
intros x y Hb;simpl in Hb.
rewrite  (rootOfTree x x_is_a_node) in Hb;rewrite (ZSet.in_single _ _ Hb).
intros x y H3;elim (H0 x y);trivial.
intros Ha [Hb | Hb].
apply H0;trivial.

unfold Ple
    intro p2; case p2; simpl in |- *. (* seven sub goals *)
        
	  (* top void *)
	  unfold Ple_complete in |- *;intros _ H;elimtype False.
simpl in H;eapply H.

;exact (H rootNotEmpty).
	 (* top top *)
	  constructor.
	 (*top (union x x0) *)
	  intros pp1 pp2 H; unfold Ple_complete in |- *; intro H1;
	  elim (H1 rootNotEmpty);intro H2;[
	      apply c2;
	      apply IHn1;[
	          apply le_S_n; eapply max_le_L;rewrite max_SS in H;apply H
		| trivial
		]
	    | apply p_gene_R;exists (union pp2 pp1);split;
	      [
	          apply c2;apply IHn1;[ 
                             simpl;apply le_S_n;rewrite max_SS in H;eapply max_le_R;apply H 
                           | trivial 
                           ]
		| (* (Pequiv (union x0 x) (union x x0)) *)
		  apply comm_union
	      ] 
	    ].

	(*top (inter x x0) *)
	  intros pp1 pp2 H;unfold Ple_complete;intro H1;apply i2;
	  apply IHn1;[	      
	        simpl;apply le_S_n; eapply max_le_L;rewrite max_SS in H;apply H
	      | intro H2;assert(HH:=H1 H2);simpl in HH;elim HH;trivial
	      | simpl;apply le_S_n; eapply max_le_R;rewrite max_SS in H;apply H
	      | intro H2;assert(HH:=H1 H2);simpl in HH;elim HH;trivial
	      ].
	 (*top (slash x x0) *)
	  unfold Ple_complete in |- *; intros.
Focus.
apply top_slash;split;apply IHn1.
simpl;LeS;simpl in H;eapply max_le_L;apply H.
intro H1;elim (H0 H1).
intros x2 [H2 H3].
simpl in H1.
simpl 
induction x0.
(* top void/x1 ------------------------------------------------------------*)
elim (H0 rootNotEmpty);intros xx [ H1 H2];inversion H1.

(* top <= top/x1 ------------------------------------------------------------*)
    Focus 1.
    induction x1.
    (* top <= top/void *)
    elim (H0 rootNotEmpty);intros xx [ H1 H2];inversion H2.
    (* top <= top/top *)    
    apply p_gene_L.
    exists (slash top top) ;split;[ apply Ple_reflexive | idtac].
    eapply Pequiv_trans.
    rewrite Pequiv_sym;apply equ_top_qualif_top.
    rewrite Pequiv_sym;apply equ_top_slash.
    simpl;trivial.
    (* top <= top/(x11| x12 *)
    assert (H1:=H0 rootNotEmpty);elim H1;intros x0 [H2 H3].
    elim H3;intro H4.
   (* left branch      H4 : Rp tree x1_1 x0 y    *) 
   apply p_gene_R; exists (union (slash top x1_1) (slash top x1_2)).
    split.
    apply c2.
    apply IHx1_1.
    simpl;LeS;simpl in H;apply le_n_S;assert (H5:= le_Smn_mn _ _ H);eapply max_le_L; apply H5.
    intro H5;simpl;exists x0;split;trivial.
    rewrite Pequiv_sym; apply equ_d_slash_union_R.
  (* right branch      H4 : Rp tree x1_2 x0 y    *) 
   apply p_gene_R; exists (union (slash top x1_1) (slash top x1_2)).
    split.
    apply p_gene_R;exists (union (slash top x1_2) (slash top x1_1));split;[apply c2 | apply comm_union].
    apply IHx1_2.
    simpl;LeS;simpl in H;apply le_n_S;assert (H5:= le_Smn_mn _ _ H);eapply max_le_R; apply H5.
    intro H5;simpl;exists x0;split;trivial.
    rewrite Pequiv_sym; apply equ_d_slash_union_R.
    (* top <= top/(x11 & x12 *)
    Focus.
    assert (H1:=H0 rootNotEmpty);elim H1;intros x0 [H2 H3].
    elim H3;intros H4 H4b.
   apply p_gene_R; exists (inter (slash top x1_1) (slash top x1_2)).
   split.
   apply i2; simpl in H.
   apply IHx1_1.
   simpl;LeS;apply le_n_S;assert (H5:= le_Smn_mn _ _ H);eapply max_le_L; apply H5.
   intro H5;simpl;exists x0;split;trivial.
   apply IHx1_2.
   simpl;LeS;apply le_n_S;assert (H5:= le_Smn_mn _ _ H);eapply max_le_R; apply H5.
   intro H5;simpl;exists x0;split;trivial.
   rewrite Pequiv_sym; constructor.  
    (* top <= top/(x11| x12 *)
    Focus.
    assert (H1:=H0 rootNotEmpty);elim H1;intros x0 [H2 H3].
    elim H3;intros y0 [ H4 H5 ].
 

    assert (H1:=H0 rootNotEmpty);
	  exists (slash top top); split.
	      (* Ple (slash top top) (slash x x0) *)
          apply d2;apply IHn1.
          simpl; apply le_S_n;eapply max_le_L;rewrite max_SS in H;apply H.
          intro H1;elim (H0 H1).
          intros x2 [H2];intro H3.
          apply H1.

         [
	      (* Ple (slash top top) (slash x x0) *)
	      
	    | (* Pequiv top (slash top top) *)
	  ].
	  
	(*top (qualif x x0) *)
	(*top (step a n0) *)	  
	
   <Your Tactic Text here>
   <Your Tactic Text here>
   intros x0 x1 p2; case p2.
    simpl in |- *.
      <Your Tactic Text here>
    <Your Tactic Text here>
    <Your Tactic Text here>
    <Your Tactic Text here>
    intros x2 x3.
      simpl in |- *.
      unfold Ple_complete in |- *.
      intros.
      constructor.
     constructor.
      apply IHn1.
       <Your Tactic Text here>
       <Your Tactic Text here>
      <Your Tactic Text here>
     <Your Tactic Text here>
    <Your Tactic Text here>
    <Your Tactic Text here>
   <Your Tactic Text here>
   <Your Tactic Text here>
   (*------------------------- Qualifiers ------------------  *)
  <Your Tactic Text here>

Abort.



			    
			   
