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
Require Export XPathInduction.
Require Import XPathGrammar.

(* simple test to determine if a path is absolute or relative *)
(* it is relative if the result depends from the contextual node, absolute otherwise *)
(* note that this definition justifies considering ⊥ as an absolute path, just as  ⋀ *)
(* this is also required for consistency .... as shown by  ⋀/a ∩ ⋀/b which must be *)
(* considered as abolute whereas equivalent to ⊥ *)
(* one can consider it extends the usual "semantics" of absolute path, understood as *)
(* "a path starting from the root node" *)
(* JYVD , 07/19/2004 *)
Fixpoint absolute (p:XPath) : Prop :=
  match p with
  | ⊥ => True
  | ⋀ => True
  | p1 ⎮ p2 => absolute p1 /\ absolute p2
  | inter p1 p2 => absolute p1 /\ absolute p2
  | slash p1 p2 => absolute p1 
  | qualif p  q  => absolute p 
  | step a n => False
  end
.

Theorem absolute_decidable: forall p:XPath, (absolute p) \/ ~(absolute p).
induction p.
left;simpl;trivial.
left;simpl;trivial.
simpl.
elim IHp1;elim IHp2;intros.
left;split;trivial.
right;intro;elim H1;intros H2 H3;apply H;exact H3.
right;intro;elim H1;intros H2 H3;apply H0;exact H2.
right;intro;elim H1;intros H2 H3;apply H0;exact H2.

simpl.
elim IHp1;elim IHp2;intros.
left;split;trivial.
right;intro;elim H1;intros H2 H3;apply H;exact H3.
right;intro;elim H1;intros H2 H3;apply H0;exact H2.
right;intro;elim H1;intros H2 H3;apply H0;exact H2.

simpl;exact IHp1.
simpl;exact IHp.
simpl;right;intro H;trivial.
Qed.

(*
Fixpoint inter_axis (a1 a2:Axis) {a1: struct} : (Option Axis) :=

Fixpoint inter_comp (p1 p2:XPath) {struct:p1} : XPath :=
match p1,p2 with 
| void, _ => void
| _,void  => void
| top, top => top
| (step a1 n1), (step a2 n2) => 
	match (inter_axis n1 n2) with 
        | (Some a) => match (inter_ntest n1 n2) with 
                              | (Some n) => (step a n)
                              | _ => void
                              end
         | _ => void
         end
| (slash p1 (step child n1)), (slash p2 (step descendant n2)) =>             
       match (inter_ntest n1 n2) with 
       | (Some n) => (slash (inter_comp p1 p2) (step a n))
       | _ => void
       end    
end
.
*)

Inductive Pequiv: XPath -> XPath -> Prop :=

  | equ_qual:
      forall p: XPath,
      Pequiv p (p[_true])
  | equ_void_qual_L:
      forall q : XQualif,
      Pequiv (⊥[q]) (⊥)
  | equ_void_qual_R:
      forall p: XPath,
      Pequiv (p[_false]) (⊥)
  | equ_void_slash_L:
      forall p: XPath,
      Pequiv (⊥/p) (⊥)
  | equ_void_slash_R:
      forall p: XPath,
      Pequiv (p/⊥) (⊥)

  | equ_self_slash_L: forall p:XPath, Pequiv p (∙/p)
  | equ_self_slash_R: forall p:XPath, Pequiv p (p/∙)
  | equ_top_slash:
      forall p:XPath,
      (absolute p) -> Pequiv (p/⋀) (⋀[# p])
  | equ_top_qualif_top:
      forall p:XPath,
      Pequiv (p[# ⋀]) p
      
  (* commutativity *)
  | comm_union:  forall p1 p2 : XPath,  Pequiv (p1 ⎮ p2) (p2 ⎮ p1)
  | comm_inter:  forall p1 p2 : XPath,  Pequiv (p1 ∩ p2) (p2 ∩ p1)
  
  (* associativity *)
  | assoc_slash:
      forall p1 p2 p3 : XPath,
      Pequiv ((p1/p2)/p3) (p1/(p2/p3))
  | assoc_union:
      forall p1 p2 p3 : XPath,
      Pequiv ( ( p1 ⎮ p2) ⎮ p3) ( p1 ⎮ ( p2 ⎮p3))
  | assoc_inter:
      forall p1 p2 p3 : XPath,
      Pequiv ((p1 ∩ p2) ∩ p3) (p1 ∩ (p2 ∩ p3))
  | assoc_qual:
      forall p : XPath,
      forall q1 q2 : XQualif,
      Pequiv (p[q1][q2])  (p[q1 and q2])
(*      Pequiv (qualif (qualif p q1) q2) (qualif p (and q1 q2)) *)

  (* structural congruence *)

  | equ_s_slash_L: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv (p1/p3) (p2/p3)
  | equ_s_slash_R: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv (p3/p1) (p3/p2)

  | equ_s_union_L: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv ( p1 ⎮ p3) ( p2 ⎮ p3)
  | equ_s_union_R: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv ( p3 ⎮ p1) ( p3 ⎮ p2)

  | equ_s_inter_L: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv (p1 ∩ p3) (p2 ∩ p3)
  | equ_s_inter_R: forall p1 p2 p3:XPath,
    Pequiv p1 p2 -> Pequiv ( p3 ∩ p1) ( p3 ∩ p2)

  | equ_s_qualif_L:
      forall p1 p2:XPath,
      forall q:XQualif,
      Pequiv p1 p2 ->
      Pequiv (p1[q]) (p2[q])

  | equ_s_qualif_R:
      forall p:XPath,
      forall q1 q2:XQualif,
      Qequiv q1 q2 ->
      Pequiv (p[q1]) (p[q2])

  (* distribution *)
  | equ_d_slash_union_L:
      forall p1 p2 p:XPath,
      Pequiv ((p1 ⎮ p2)/p) ( (p1/p) ⎮ (p2/p))
  | equ_d_slash_union_R:
      forall p1 p2 p:XPath,
      Pequiv (p/(p1 ⎮ p2)) ((p/p1) ⎮ (p/p2))
  | equ_d_inter_union_L:
      forall p1 p2 p:XPath,
      Pequiv ( (p1 ⎮ p2) ∩ p) (( p1 ∩ p) ⎮ ( p2 ∩ p))
  | equ_d_inter_union_R:
      forall p1 p2 p:XPath,
      Pequiv ( p ∩ (p1 ⎮ p2)) (( p ∩ p1) ⎮ ( p ∩ p2))

with Preduce:  XPath -> XPath -> Prop :=
  | red_d_slash_inter_L:
      forall p1 p2 p:XPath,
      Preduce ((p1 ∩ p2)/p) ( (p1/p)  ∩ (p2/p))
  | red_d_slash_inter_R:
      forall p1 p2 p:XPath,
      Preduce (p/(p1 ∩ p2)) ((p/p1) ∩ (p/p2))
   | red_gen:
      forall p1 p2 :XPath,
      (Pequiv p1 p2) -> (Preduce p1 p2)
 
with Qequiv:  XQualif -> XQualif -> Prop :=
      
  (* computation like *)      
  | equ_or_false_L:
      forall q : XQualif,
      Qequiv (q or _false) q
  | equ_or_false_R:
      forall q : XQualif,
      Qequiv (_false or q) q
  | equ_or_true_L:
      forall q : XQualif,
      Qequiv (q or _true) _true
  | equ_or_true_R:
      forall q : XQualif,
      Qequiv (_true or q) _true
  | equ_not_true:  Qequiv (not _true) _false
  | equ_not_false: Qequiv (not _false) _true
      
  | equ_and_true_L:
      forall q : XQualif,
      Qequiv (q and _true) q
  | equ_and_true_R:
      forall q : XQualif,
      Qequiv (_true and q) q
  | equ_and_false_L:
      forall q : XQualif,
      Qequiv (q and _false) _false
  | equ_and_false_R:
      forall q : XQualif,
      Qequiv (_false and q) _false
      
  | equ_not_not:
      forall q: XQualif,
      Qequiv (not (not q)) q
  
  | equ_not_or:
      forall q1 q2: XQualif,
      Qequiv (not (q1 or q2)) ((not q1) and (not q2) )

  (* commutativity *)
  | comm_and:  forall q1 q2 : XQualif,  Qequiv (q1 and q2) (q2 and q1)
  | comm_or:   forall q1 q2 : XQualif,  Qequiv (q1 or q2) (q2 or q1)
  
  (* associativity *)      
  | assoc_and:
      forall q1 q2 q3 : XQualif,
      Qequiv ((q1 and q2) and q3) (q1 and (q2 and q3))
  | assoc_or:
      forall q1 q2 q3 : XQualif,
      Qequiv ((q1 or q2) or q3) (q1 or (q2 or q3))
      
  (* structural congruence *)

  | equ_s_and_L: forall q1 q2 q3:XQualif,
    Qequiv q1 q2 -> Qequiv (q1 and q3) (q2 and q3)    
  | equ_s_and_R: forall q1 q2 q3:XQualif,
    Qequiv q1 q2 -> Qequiv (q3 and q1) (q3 and q2)

  | equ_s_or_L: forall q1 q2 q3:XQualif,
    Qequiv q1 q2 -> Qequiv (q1 or q3) (q2 or q3)    
  | equ_s_or_R: forall q1 q2 q3:XQualif,
    Qequiv q1 q2 -> Qequiv (q3 or q1) (q3 or q2)
    
  | equ_s_not: forall q1 q2:XQualif,
    Qequiv q1 q2 -> Qequiv (not q1) (not q2)

  | equ_s_leq_L:
      forall p1 p2 p3:XPath,
      Pequiv p1 p2 ->
      Qequiv (p1 ⊑ p3) (p2 ⊑ p3)
  | equ_s_leq_R:
      forall p1 p2 p3:XPath,
      Pequiv p2 p3 ->
      Qequiv (p1 ⊑ p2) (p1 ⊑ p3)
 .

Notation "p1 ⇽⇾ p2" := (Pequiv p1 p2) (at level 90, no associativity) : Xrel.
Notation "p1 ⇾ p2" := (Preduce p1 p2) (at level 90, no associativity) : Xrel.
Notation "q1 ⇐⇒ q2" := (Qequiv q1 q2) (at level 90, no associativity) : Xrel.


Require Import XPathSemantics.
Require Import XPathSemanticsEquivalences.

Open Scope Xrel.



(* Pequiv and Qequiv must be equivalence relations *)
Axiom Pequiv_reflexive: forall p:XPath, (p ⇽⇾ p).
Axiom Qequiv_reflexive: forall q:XQualif,  q ⇐⇒ q.

Axiom Pequiv_symmetric: forall p1 p2:XPath, (p1 ⇽⇾ p2) = (p2 ⇽⇾ p1).
Axiom Qequiv_symmetric: forall q1 q2:XQualif, (q1 ⇐⇒ q2)=(q2 ⇐⇒ q1).

Axiom Pequiv_transitive: forall p1 p2 p3:XPath, p1 ⇽⇾ p2 -> p2 ⇽⇾ p3 -> p1 ⇽⇾ p3.
Axiom Qequiv_transitive: forall q1 q2 q3:XQualif, q1 ⇐⇒ q2 -> q2 ⇐⇒ q3 -> q1 ⇐⇒ q3.

(*
Ltac solvePEqu :=
  match goal with
  (Pequiv ?p1 (slash dot ?p2)) => apply
  (Pequiv ?p1 ?p2) => constructor
  end
  with
  solveQequ :=
  match goal with
  end
  .
*)
 (* Open Scope Xp.
Open Scope Xq. *)
