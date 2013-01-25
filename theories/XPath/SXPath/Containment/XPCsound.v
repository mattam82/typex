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
Require Import XPathGrammar.
Require Export XPathSemantics.
Require Export XPCAxioms.
Require Export XPathInduction.
Require Import nat_basics.
Require Import graphInt.
Require Import graphProp.
(* Require mesure. *)

(* defines also context tree and context node x *)
(*Require Import hypotheses.
Require Import forall_exists.
*)
Require Import XPequiv.
(* Require Import XPCsound. *)

Variable tree : Tree.
Hypothesis wfXml : wfXmlTree tree.

Lemma nametest: 
   forall y:NodeId,
   forall a : XName.A,
   test_node tree (!a) y = true -> (
     XTree.get_node tree y = Some (element a)
     \/  (exists v:XValues.A, XTree.get_node tree y = Some (attr a v))
     \/  XTree.get_node tree y = Some (nmspace a)
     ).
intros y a;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intro a0;cut ({XName.A_eq a0 a = true} + {XName.A_eq a0 a = false}); [ intros [Ha | Ha] | apply XName.dec ].
intros _;rewrite (XName.eq_struct a0 a);Sbase.
rewrite Ha;intro;discriminate.
intros a0 a1;cut ({XName.A_eq a0 a = true} + {XName.A_eq a0 a = false}); [ intros [Ha | Ha] | apply XName.dec ].
intros _;rewrite (XName.eq_struct a0 a);Sbase.
right;left;exists a1;reflexivity.
rewrite Ha;intro;discriminate.
intro a0;cut ({XName.A_eq a0 a = true} + {XName.A_eq a0 a = false}); [ intros [Ha | Ha] | apply XName.dec ].
intros _;rewrite (XName.eq_struct a0 a);Sbase.
rewrite Ha;intro;discriminate.
Qed.

Lemma elementtest: 
   forall y:NodeId,
   test_node tree (_element) y = true -> (exists a:XName.A,XTree.get_node tree y = Some (element a))
   .
intro y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros;exists a;reflexivity.
Qed.

Lemma attributetest: 
   forall y:NodeId,
   test_node tree (_attribute) y = true -> (
     exists a:XName.A,
     exists v:XValues.A, 
     XTree.get_node tree y = Some (attr a v)
     ).
intro y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros;exists a;exists a0;reflexivity.
Qed.


Lemma startest: 
   forall y:NodeId,
   test_node tree _any y = true -> (
     (exists a:XName.A, XTree.get_node tree y = Some (element a))
     \/  (exists a:XName.A, exists v:XValues.A,XTree.get_node tree y = Some (attr a v))
     \/  (exists a:XName.A, XTree.get_node tree y = Some (nmspace a))
     ).
intros y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros a _;left;exists a;reflexivity.
intros a v _;right;left;exists a;exists v;reflexivity.
intros a _;right;right;exists a;reflexivity.
Qed.

Lemma commenttest: 
   forall y:NodeId,
   test_node tree (_comment) y = true -> (exists a:XName.A,XTree.get_node tree y = Some (comment a))
   .
intro y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros;exists a;reflexivity.
Qed.

Lemma texttest: 
   forall y:NodeId,
   test_node tree (_text) y = true -> (exists a:XName.A,XTree.get_node tree y = Some (text a))
   .
intro y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros;exists a;reflexivity.
Qed.

Lemma pitest: 
   forall y:NodeId,
   test_node tree (_pi) y = true -> (exists a:XName.A,exists i:XInstr.A,XTree.get_node tree y = Some (pi a i))
   .
intro y;unfold test_node.
case (XTree.get_node tree y);[intro n | intro;discriminate].
case n;try (intros;discriminate).
intros;exists a;exists a0;reflexivity.
Qed.

Scheme XPLL := Minimality for Ple Sort Prop
  with XQLL := Minimality for Qipl Sort Prop.

Scheme XPLI := Induction for Ple Sort Prop
  with XQLI := Minimality for Qipl Sort Prop.


Ltac S1 :=
(* 
ntest_le descendant-or-self n1 n2
test_node tree n1 y = true
*)
match goal with [ 
  H0: ntest_le _ ?n1 ?n2, 
  H4: test_node ?tree ?n1 ?y = true
  |- test_node ?tree ?n2 ?y = true
  ] => 
generalize H0;generalize H4;case n1;case n2;simpl;try (intros;contradiction);auto;
[
    intros a a0 Ha Hb;rewrite <- Hb;exact Ha
  | intros a Ha _;elim (nametest y a Ha);[
      intro Hb;unfold test_node;rewrite Hb;reflexivity
    | intros [[v Hb]|Hb];unfold test_node;rewrite Hb;reflexivity
    ]
|
  intros a Ha _;elim (nametest y a Ha);[
  intro Hb;unfold test_node;rewrite Hb;reflexivity
  | intros [[v Hb]|Hb];unfold test_node;rewrite Hb;reflexivity
  ]
|
intro Ha;elim (startest _ Ha);[
  intros [a Hb] _;unfold test_node;rewrite Hb;reflexivity
  | intros [[a [v Hb]]| [ a Hb]];unfold test_node;rewrite Hb;reflexivity
 ]
|
intros Ha _;elim (elementtest y Ha);intros x0 Hb;unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (elementtest y Ha);intros x0 Hb;unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (attributetest y Ha);intros x0 [v Hb];unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (attributetest y Ha);intros x0 [v Hb];unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (commenttest y Ha);intros x0 Hb;unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (texttest y Ha);intros x0 Hb;unfold test_node;rewrite Hb;reflexivity
|
intros Ha _;elim (pitest y Ha);intros x0 [v Hb];unfold test_node;rewrite Hb;reflexivity
]
end.



(* PPR is defined in XPEsound *)

Lemma le_sound:  
  forall p1 p2:XPath,  
  p1 ≤ p2  -> PPR p1 p2 
.
apply XPLL
 with  (P0 := fun q1 q2:XQualif => 
		    forall x :NodeId,
		   (x∊tree) ->
		   ((Rq tree q1 x ) -> (Rq tree q2 x ))
          ) ;unfold PPR.

simpl;intros;contradiction.
simpl;intros;trivial.

(*===============================================*)
(*                 a1 ≤  a2                             n1 ≤ n2                                   *)
(*   ------------------------------------------------------------------------------     *)
(*                              a1 :: n1  ≤  a2 :: n2                                              *)
(*===============================================*)
Focus.
intros a1 a2 n1 n2 H1 H2 x y x_in_tree y_in_tree;simpl.
generalize H1.
generalize H2.
case a1;case a2;simpl;auto;try (intros;contradiction).
case n1;case n2;simpl;auto;try (intros;contradiction);try (intro;Sbase).

intros a0 H;rewrite H;Sbase.
elim (nametest y a H4).
intro Ha;unfold test_node;rewrite Ha;reflexivity.
intros [ [v Ha] | Ha];unfold test_node;rewrite Ha;reflexivity.

elim (elementtest y H4).
intros x0 Ha;unfold test_node;rewrite Ha;reflexivity.

elim (attributetest y H4).
intros x0 [v Ha];unfold test_node;rewrite Ha;reflexivity.

solve [Sbase;[apply ZSet.in_unionL;exact H | S1]].
solve [Sbase;S1].
solve [Sbase;S1].
solve [Sbase;S1].
solve [Sbase;[ apply XTree.children_descendants;trivial | S1]].
solve [Sbase;[ apply ZSet.in_unionR;trivial;apply XTree.children_descendants;trivial | S1]].
solve [Sbase;S1].
solve [Sbase;[ apply ZSet.in_unionR;trivial | S1]].
solve [Sbase;S1].

Focus 8.
(*===============================================*)
(*                                                                                                          *)
(*          p1 ≤ p2                                  q1 ⇨ q2                                     *)
(*   ------------------------------------------------------------------------------     *)
(*                            p1[q1]  ≤  p2[q2]                                                  *)
(*                                                                                                          *)                              
(*===============================================*)
intros p1 p2 q1 q2 H1 I1 H2 I2 x y x_in_tree y_in_tree;simpl.
intros [Ha Hb];split;auto.

Focus 3.
(*===============================================*)
(*                                                                                                          *)                              
(*      p11[#p12] ≤ p21[#p22]                    p12 ≤ p22                          *)
(*   ------------------------------------------------------------------------------     *)
(*                 p11 / p12  ≤  p21 / p22                                                    *)
(*                                                                                                          *)                              
(*===============================================*)
intros.
simpl.
simpl in H5.
elim H5;intros z [Ha Hb].
exists z;split;[ idtac | apply H2;trivial;Sbase].
simpl in H0.
cut (z ∊ tree);[ intro z_in_tree | Sbase].
generalize (H0 x z H3 z_in_tree).
intro Hc.
cut (~ (forall z0 : NodeId, Ƥ [p12](tree, z ↝  z0) -> False)).
intro Hd;
cut (Ƥ [p11](tree, x ↝  z) /\  ~ (forall z0 : NodeId, Ƥ [p12](tree, z ↝  z0) -> False)).
intro He; elim (Hc He);intros;trivial.
split;trivial.
Require Import Classical.
apply ex_not_not_all with (P:=(fun zz:NodeId => ~ Ƥ [p12](tree, z ↝  zz))).
exists y.
auto.

Focus.
(*===============================================*)
(*                                                                                                          *)                              
(*      p1 ≤ descendant::node()        p2 ≤ descendant::n2[q]                 *)
(*   ------------------------------------------------------------------------------     *)
(*                 p1 / p2  ≤  descendant::n2[q]                                           *)
(*                                                                                                          *)                              
(*===============================================*)
intros p1 p2 n2 q H1 I1 H2 I2 x y x_in_tree y_in_tree Ha.
elim Ha;intros z [ Hb Hc].
cut (z ∊ tree);[ intro z_in_tree | Sbase].
generalize (I1 x z x_in_tree z_in_tree Hb);intro Hd.
generalize (I2 z y z_in_tree y_in_tree Hc);intro He.

simpl;simpl in Hd;simpl in He;Sbase.
eapply XTree.descendants_closure;eauto.

Focus.
(*===============================================*)
(*                                                                                                          *)
(*      descendant::%node()/p ⇨ q1             p ≤ descendant::n[q]          *)
(*   ------------------------------------------------------------------------------     *)
(*                          p  ≤  ⋀[q1]/descendant::n[q]                                    *)
(*                                                                                                          *)
(*===============================================*)
intros p q1 q n H1 I1 H2 I2 x y x_in_tree y_in_tree Ha.

exists root;split.
split.
simpl;rewrite rootOfTree;trivial;apply ZSet.single_sem.
apply I1.
apply root_in_tree.
simpl.
intro Hb;eapply Hb.
exists x;split;[split; [ apply tree_connected | apply allNodesMatch];trivial | apply Ha].
simpl.
simpl in I2;generalize (I2 x y x_in_tree y_in_tree Ha);Sbase.
apply tree_connected;trivial.

Focus.
(*===============================================*)
(*                                                                                                          *)
(*              p ≤ p1                                       p ≤ p2                                *)
(*   ------------------------------------------------------------------------------     *)
(*                                  p  ≤  p1 ∩ p2                                                    *)
(*                                                                                                          *)
(*===============================================*)
intros p1 p2 p H1 H2 I1 I2 x y x_in_tree y_in_tree Ha.
simpl;Sbase;auto.

Focus.
(*===============================================*)
(*                                                                                                          *)
(*                                      p1 ≤ p                                                          *)
(*   ------------------------------------------------------------------------------     *)
(*                                  p1 ∩ p2  ≤  p                                                    *)
(*                                                                                                          *)
(*===============================================*)
intros p1 p2 p H1 I1 x y x_in_tree y_in_tree;simpl;Sbase;auto.

Focus.
(*===============================================*)
(*                                                                                                          *)
(*                  p1 ≤ p                                  p2 ≤ p                                 *)
(*   ------------------------------------------------------------------------------     *)
(*                                  p1 ⎮ p2  ≤  p                                                    *)
(*                                                                                                          *)
(*===============================================*)
intros p1 p2 p H1 I1 H2 I2 x y x_in_tree y_in_tree;simpl;Sbase;auto.

Focus.
(*===============================================*)
(*                                                                                                          *)
(*                                        p ≤ p1                                                        *)
(*   ------------------------------------------------------------------------------     *)
(*                                  p ≤  p1 ⎮ p2                                                    *)
(*                                                                                                          *)
(*===============================================*)
intros p1 p2 p H1 I1  x y x_in_tree y_in_tree;simpl;Sbase;auto.

intros p11 p12 p21 p22 H1 I1 H2 I2 x x_in_tree ;simpl.
intros Ha z Hb;cut (z ∊ tree);[ intro z_in_tree | Sbase].
apply I2;auto.

intros q1 q2 H I x x_in_tree ;simpl;auto.
intros;simpl;auto.
intros q x x_in_tree;simpl;contradiction.
intros q11 q12 q H I x x_in_tree ;simpl;Sbase;auto.

intros q1 q21 q22 H1 I1 H2 I2 x x_in_tree ;simpl;Sbase;auto.
intros q1 q21 q22 H1 I1 x x_in_tree ;simpl;Sbase;auto.
intros q11 q12 q2 H1 I1 H2 I2 x x_in_tree ;simpl;Sbase;auto.

intros nt H x x_in_tree Ha.
simpl in Ha.
simpl.
intros z [Hb Hc].
generalize (XTree.descendants_sem2 tree x z Hb).
intros [Hd | Hd].
apply (Ha z);split.
trivial.

generalize H Hc.
case nt;simpl;intros;try contradiction.
unfold test_node .
elim (elementtest _ Hc0);intros y He;rewrite He;reflexivity.

elim Hd.
intros y [He Hf].
apply (Ha y).
split;trivial.
unfold test_node.

elim (XTree.descendants_sem2 tree _ _ Hf).
intro Hg.
generalize (elements_only_have_desc _ _ Hg).

intros [ [nm Hh] | Hh];rewrite Hh.
reflexivity.
elimtype False;generalize (a_child_is_never_a_root _ _ He).
intro;contradiction.

intros [ w [Hg Hh ]];
generalize (elements_only_have_desc _ _ Hg).
intros [ [nm Hi] | Hi];rewrite Hi.
reflexivity.
elimtype False;generalize (a_child_is_never_a_root _ _ He).
intro;contradiction.
Qed.

Theorem  p_gene_L_sound:
      forall p1 p2 p3:XPath,
      (p1 ⇾ p2) -> 
      (p2 ≤ p3)  -> 
      (PPR p2 p3) ->
      p1 ≤ p3 -> (PPR p1 p3)
      .
intros p1 p2 p3 H1 H2 H3 H4.
assert (H5:=red_sound _ _ H1).
unfold PPR.
auto.
Qed.

Theorem  p_gene_R_sound:
      forall p1 p2 p3:XPath,
      (p2 ⇾ p3) -> 
      (p1 ≤ p2)  -> 
      (PPR p1 p2) ->
      p1 ≤ p3 -> (PPR p1 p3)
      .
intros p1 p2 p3 H1 H2 H3 H4.
assert (H5:=red_sound _ _ H1).
unfold PPR.
auto.
Qed.
