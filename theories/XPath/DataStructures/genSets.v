(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import ZArith.
Require Import setOrder.
Require Import Bool.
Require Import genSetsInt.


Module geneSets (theorder: CmpOrderTheory) : genSetsInt with Definition
  A := theorder.A with Definition A_le := theorder.le with Definition
  A_lt := theorder.lt with Definition A_eq := theorder.eq. 

Definition A := theorder.A.
Definition A_le := theorder.le.
Definition A_lt := theorder.lt.
Definition A_eq := theorder.eq. 



(* ----------------------------------------------------------------- *)
(*	the data structure, very much like lists                     *)

Inductive set : Set :=
  | empty : set
  | item : A -> set -> set.
 
Definition single (x : A) := item x empty.

(*  -----------------------------------------------------------------
     tests the membership
 ----------------------------------------------------------------- 
Fixpoint s_in [a:A;s:set]: bool :=
Cases s of 
| empty => false
| (item b ss) => if (A_le b a) 
	         then 
		      if (A_le a b) 
		      then true
		      else (s_in a ss)
		 else 
 		      false
end.
*)



(*  -----------------------------------------------------------------
     tests the membership (simplified)
 ----------------------------------------------------------------- *)

Fixpoint s_in (a : A) (s : set) {struct s} : bool :=
  match s with
  | empty => false
  | item b ss => if A_eq a b then true else s_in a ss
  end.




(*  -----------------------------------------------------------------
     Concatenation of two sets
 ----------------------------------------------------------------- *)

Fixpoint cat (s1 s2 : set) {struct s1} : set :=
  match s1 with
  | empty => s2
  | item a ss1 => item a (cat ss1 s2)
  end.


(* ---------------------------------------------------------------- *)
(* Well formedness: all items are unique in the set, and ordered    *)
(*----------------------------------------------------------------- *)
Fixpoint wf (s : set) : bool :=
  match s with
  | empty => true
  | item a ss =>
      if s_in a ss
      then false
      else
       if wf ss
       then match ss with
            | item b _ => A_lt a b
            | empty => true
            end
       else false
  end.



(* -----------------------------------------------------------------
	cardinal of sets. Always positive Z 
-----------------------------------------------------------------  *)
Fixpoint card (s : set) : Z :=
  match s with
  | empty => 0%Z
  | item _ ss => Zsucc (card ss)
  end.
(* Zs is the successor function for Z *)


(* -----------------------------------------------------------------
	constructors and tests 
-----------------------------------------------------------------  *)

Fixpoint add (a : A) (s : set) {struct s} : set :=
  match s with
  | empty => item a empty
  | item b ss =>
      if A_le b a
      then if A_le a b then s else item b (add a ss)
      else item a s
  end.

Fixpoint sub (a : A) (s : set) {struct s} : set :=
  match s with
  | empty => empty
  | item b ss =>
      if A_le b a then if A_le a b then ss else item b (sub a ss) else s
  end.

Section set_reduction.

 Variable B : Set.
 Fixpoint reduce (f : B -> A -> B) (b : B) (s : set) {struct s} : B :=
   match s with
   | empty => b
   | item a ss => reduce f (f b a) ss
   end.

End set_reduction.



  Fixpoint inter (x : set) : set -> set :=
    match x with
    | empty => fun y => empty
    | item a1 x1 =>
        fun y => if s_in a1 y then item a1 (inter x1 y) else inter x1 y
    end.

  Fixpoint union (x y : set) {struct y} : set :=
    match y with
    | empty => x
    | item a1 y1 => add a1 (union x y1)
    end.

        
  (** returns the set of all els of [x] that does not belong to [y] *)
  Fixpoint diff (x y : set) {struct x} : set :=
    match x with
    | empty => empty
    | item a1 x1 => if s_in a1 y then diff x1 y else item a1 (diff x1 y)
    end.



    Fixpoint incl (s1 s2 : set) {struct s1} : bool :=
      match s1 with
      | empty => true
      | item a s => if s_in a s2 then incl s s2 else false
      end.

    Fixpoint s_eq (s1 s2 : set) {struct s2} : bool :=
      match s1, s2 with
      | empty, empty => true
      | item a1 ss1, item a2 ss2 =>
          if A_eq a1 a2 then s_eq ss1 ss2 else false
      | _, _ => false
      end.
(*
    Definition s_eq:set->set->bool :=
	[s1,s2:set]
	if (incl s1 s2) then (incl s2 s1) else false
	.
*)
    Fixpoint product (s : set) (fs : A -> set) {struct s} : set :=
      match s with
      | empty => empty
      | item a s1 => union (fs a) (product s1 fs)
      end.


    Fixpoint filter (s : set) (fs : A -> bool) {struct s} : set :=
      match s with
      | empty => empty
      | item a s1 => if fs a then item a (filter s1 fs) else filter s1 fs
      end.




(* ----- Properties ------- *)




Axiom not_single_empty : forall x : A, single x <> empty.
Axiom single_sem : forall x : A, s_in x (single x) = true.
Axiom in_single : forall x y : A, s_in x (single y) = true -> x=y.





(* ----- cat ------- *)
	
	
Axiom
  cat_incl :
    forall s1 s2 : set,
    wf (cat s1 s2) = true ->
    forall a : A,
    (s_in a s1 = true -> s_in a s2 = false) /\
    (s_in a s2 = true -> s_in a s1 = false).

Axiom
  cat_union :
    forall s1 s2 : set, wf (cat s1 s2) = true -> cat s1 s2 = union s1 s2.
Axiom
  cat_inter :
    forall s1 s2 : set, wf (cat s1 s2) = true -> inter s1 s2 = empty.






(* ----- in ------- *)

Theorem in_add2 : forall (a : A) (s : set), s_in a (add a s) = true.
Proof.
intros.
induction  s as [| a0 s Hrecs].
simpl in |- *.
assert (H := theorder.eq_reflexive a).
compute in |- *.
rewrite H.
reflexivity.

simpl in |- *.
cut ({A_le a a0 = true} + {A_le a a0 = false}).
cut ({A_le a0 a = true} + {A_le a0 a = false}).
intros.
elim H.
elim H0.
intros.
rewrite a1.
rewrite a2.
assert (a = a0).
apply theorder.le_antisymmetric.
assumption.

assumption.

rewrite H1.
simpl in |- *.
assert (A_eq a0 a0 = true).
apply theorder.eq_reflexive.

rewrite H2.
reflexivity.

intros.
rewrite b.
rewrite a1.
simpl in |- *.
assert (A_eq a a0 = false).
compute in |- *.
apply theorder.le_nle_neq.
assumption.

assumption.

rewrite H1.
apply Hrecs.

intros.
rewrite b.
simpl in |- *.
assert (A_eq a a = true).
apply theorder.eq_reflexive.

rewrite H1.
reflexivity.

apply theorder.le_dec.

apply theorder.le_dec.
Qed.



Theorem in_add :
 forall (a : A) (s : set),
 s_in a s = true -> forall b : A, s_in a (add b s) = true.
Proof.
simple induction s.
simpl in |- *.
intros.
discriminate.

intros.
assert ({A_eq a b = true} + {A_eq a b = false}).
apply theorder.eq_dec.

elim H1.
intro.
assert (a = b).
apply theorder.eq_eq.
compute in a1.
assumption.

rewrite H2.
apply in_add2.

intro.
simpl in |- *.
cut ({A_le a0 b = true} + {A_le a0 b = false}).
cut ({A_le b a0 = true} + {A_le b a0 = false}).
intros.
elim H2.
elim H3.
intros.
rewrite a1.
rewrite a2.
assumption.

intros.
rewrite b1.
simpl in |- *.
rewrite b0.
unfold s_in in H0.
assumption.

intros.
rewrite b1.
elim H3.
intro.
rewrite a1.
simpl in |- *.
cut ({A_eq a a0 = true} + {A_eq a a0 = false}).
intros.
elim H4.
intro.
rewrite a2.
reflexivity.

intro.
rewrite b2.
apply H.
unfold s_in in H0.
rewrite b2 in H0.
exact H0.

apply theorder.eq_dec.

intro.
rewrite b2.
unfold s_in in |- *.
rewrite b0.
assumption.

apply theorder.le_dec.

apply theorder.le_dec.
Qed.









Axiom
  nin_add :
    forall (a b : A) (s : set), s_in a (add b s) = false -> s_in a s = false.

(*
Induction s.
Simpl.
Intros.
Reflexivity.

Intros.
Simpl in H0.
Cut {(A_le a0 b)=true}+{(A_le a0 b)=false}.
Cut {(A_le b a0)=true}+{(A_le b a0)=false}.
Intros.
Elim H1.
Elim H2.
Intros.
Rewrite -> a1 in H0.
Rewrite -> a2 in H0.
Assumption.

Intros.
Rewrite -> a1 in H0.
Rewrite -> b0 in H0.
Exact ((nin_succ a b (item a0 s0)) H0).

Intro.
Rewrite -> b0 in H0.
Elim H2.
Intro.
Rewrite -> a1 in H0.

 
 

Axiom nin_add2 : (a,b,c:A; s : set) (s_in a (add b (item c s)))=false->(s_in a (add b s))=false.



Axiom nin_add2 : (a,b,c:A; s : set) (s_in a (add b (item c s)))=false->(A_eq a c)=false.

*)





Theorem in_sem1 : forall a : A, s_in a empty = false. 
Proof.
auto.
Qed.

Theorem in_sem2 : forall (a : A) (s : set), s_in a (item a s) = true.
Proof.
intros; simpl in |- *; rewrite theorder.eq_reflexive; reflexivity.
Qed.


Axiom
  in_sem3 :
    forall (a : A) (s : set),
    wf s = true ->
    s_in a s = true ->
    exists s1 : set, (exists s2 : set, s = cat s1 (item a s2)).

Axiom
  in_sem4 :
    forall (a : A) (s1 s2 : set),
    wf (cat s1 s2) = true ->
    s_in a (cat s1 s2) = true -> s_in a s1 = true \/ s_in a s2 = true.


Axiom in_sem5 : forall (a b : A) (s : set), 
s_in a s = true -> s_in a (item b s) = true.

Axiom in_sem6 : forall (a b : A) (s : set), 
s_in a (item b s) = true -> ~a=b -> s_in a s = true.

Axiom
  in_Lunion :
    forall (a : A) (s1 s2 : set),
     s_in a (union s1 s2) = true -> s_in a s2 = false ->
     s_in a s1 = true.

Axiom
  in_unionL :
    forall (a : A) (s s2 : set),
    s_in a s = true -> s_in a (union s s2) = true.

Axiom
  in_unionR :
    forall (a : A) (s s2 : set),
    s_in a s = true -> s_in a (union s2 s) = true.





Axiom in_union: forall (a b : set)(y : A),
(s_in y (union a b)=true)
->((s_in y a=true) \/ (s_in y b=true)).

Axiom in_inter1: forall (a b :set) (y : A),
 (s_in y (inter a b)=true)->
((s_in y a=true) /\ (s_in y b=true)).

Axiom in_inter2: forall (a b : set) (y : A),
((s_in y a=true) /\ (s_in y b=true)) ->
(s_in y (inter a b)=true).





(* Why dealing with wf here ?
Axiom in_embedded: 
  (a,b:A;s:set) 
  (wf (item b s))=true -> 
  (s_in a s)=true -> 
  (s_in a (item b s))=true
  .
*)


Axiom
  in_embedded :
    forall (a b : A) (s : set), s_in a s = true -> s_in a (item b s) = true.




Theorem in_succ :
 forall (a b : A) (s : set),
 A_eq a b = false -> s_in a (item b s) = true -> s_in a s = true.
Proof.
intros a b s.
simpl in |- *.
case A_eq.
intro.
discriminate.
intros.
assumption.
Qed.




Theorem nin_succ :
 forall (a b : A) (s : set), s_in a (item b s) = false -> s_in a s = false.
Proof.
simple induction s.
simpl in |- *.
intros.
reflexivity.

intros.
cut ({A_eq a a0 = true} + {A_eq a a0 = false}).
intros.
elim H1.
intro.
simpl in |- *.
rewrite a1.
simpl in H0.
rewrite a1 in H0.
assert ({A_eq a b = true} + {A_eq a b = false}).
apply theorder.eq_dec.

elim H2.
intro.
rewrite a2 in H0.
discriminate.

intro.
rewrite b0 in H0.
discriminate.

intro.
simpl in |- *.
rewrite b0.
apply H.
simpl in H0.
rewrite b0 in H0.
cut ({A_eq a b = true} + {A_eq a b = false}).
intros.
elim H2.
intro.
rewrite a1 in H0.
discriminate.

intro.
rewrite b1 in H0.
simpl in |- *.
rewrite b1.
assumption.

apply theorder.eq_dec.

apply theorder.eq_dec.
Qed.



Theorem in_dec :
 forall (s : set) (a : A), {s_in a s = true} + {s_in a s = false}.
(* Obsolete : *)
(*
Proof.
Induction s.
Simpl;Auto.

Intros a0 s0 H a1.
Simpl.
Assert H1:=(theorder.le_dec a0 a1).
Assert H2:=(theorder.le_dec a1 a0).
Elim H1; Elim H2.

Intros H3 H4; Rewrite -> H3; Rewrite -> H4; Auto.
Intros H3 H4; Rewrite -> H3; Rewrite -> H4; Auto.
Intros H3 H4; Rewrite -> H3; Rewrite -> H4; Auto.
Intros H3 H4; Rewrite -> H3; Rewrite -> H4; Auto.
Qed.
*)

(* new proof for simplified version of s_in: *)
Proof.
simple induction s.
simpl in |- *; auto.

intros.
simpl in |- *.
assert (H1 := theorder.eq_dec a0 a).
elim H1.
intro.
case A_eq.
left.
reflexivity.

apply (H a0).

intro.
case A_eq.
left.
reflexivity.

apply (H a0).

Qed.



(* ----- card ------- *)


Theorem card_is_pos : forall s : set, (0 <= card s)%Z.
Proof.
simple induction s.
compute in |- *; intro H; discriminate H.
intros a l; simpl in |- *; apply Zle_le_succ.
Qed.

Theorem card_empty : card empty = 0%Z. 
Proof.
auto.
Qed.









(* ----- add ------- *)


Axiom add_sem1 : forall (a : A) (s : set), s_in a s = true -> add a s = s.
(*
Theorem add_sem1:
	(a:A;s:set)
	(s_in a s)=true -> (add a s)=s .
Proof.
Induction s.
Simpl;Intro H; Discriminate H.

Intros a1 s0 Hind;Simpl.
Case (A_le a1 a);Case (A_le a a1).
Auto.

Intro H; Assert H1:=(Hind H); Rewrite -> H1; Reflexivity.

Intro H; Discriminate H.
Abort.
*)


Theorem add_sem2 : forall (a : A) (s : set), s_in a (add a s) = true.
Proof.
intros.
case s.
simpl in |- *.
assert (H := theorder.eq_reflexive a).
compute in |- *.
rewrite H. 
reflexivity.

intros.
apply in_add2.
Qed.



Axiom add_wf : forall (a : A) (s : set), wf s = true -> wf (add a s) = true.
Axiom
  add_card1 :
    forall (a : A) (s : set),
    s_in a s = false -> card (add a s) = (card s + 1)%Z.
Axiom add_card2 : forall (a : A) (s : set), (card (add a s) >= card s)%Z.




(* ---- equality ---- *)
Axiom
  s_eq_sem : forall s1 s2 : set, s_eq s1 s2 = andb (incl s1 s2) (incl s2 s1).
Axiom
  s_eq_eq :
    forall s1 s2 : set,
    wf s1 = true -> wf s2 = true -> (s1 = s2 <-> s_eq s1 s2 = true).
Axiom
  s_neq_neq :
    forall s1 s2 : set,
    wf s1 = true -> wf s2 = true -> (s1 <> s2 <-> s_eq s1 s2 = false).

Section decidableEq.
  Axiom
    s_eq_dec : forall s1 s2 : set, {s_eq s1 s2 = true} + {s_eq s1 s2 = false}.
  Axiom s_eq_struct : forall s1 s2 : set, s_eq s1 s2 = true -> s1 = s2.
  Axiom s_eq_reflexive : forall s : set, s_eq s s = true.
  Axiom
    s_eq_symmetric :
      forall s1 s2 : set, s_eq s1 s2 = true -> s_eq s2 s1 = true.
  Axiom
    s_eq_transitive :
      forall s1 s2 s3 : set,
      s_eq s1 s2 = true -> s_eq s2 s3 = true -> s_eq s1 s3 = true.
End decidableEq.






(* ----- sub ------- *)
Axiom sub_sem1 : forall (a : A) (s : set), s_in a s = false -> sub a s = s.
Axiom sub_sem2 : forall (a : A) (s : set), s_in a (sub a s) = false.
Axiom sub_wf : forall (a : A) (s : set), wf s = true -> wf (sub a s) = true.
Axiom
  sub_card1 :
    forall (a : A) (s : set),
    s_in a s = true -> card (sub a s) = (card s - 1)%Z.
Axiom sub_card2 : forall (a : A) (s : set), (card (sub a s) <= card s)%Z.
Axiom sub_add_sem : forall (a : A) (s : set), sub a (add a s) = s.


(* ----- inter ------- *)
Axiom
  inter_semL :
    forall (a : A) (s1 s2 : set),
    s_in a s1 = true -> s_in a s2 = true -> s_in a (inter s1 s2) = true.
Axiom inter_empty : forall s : set, inter s empty = empty.
Axiom inter_incl : forall s1 s2 : set, incl s1 s2 = true -> inter s1 s2 = s1.
Axiom inter_idem : forall s : set, inter s s = s.
Axiom inter_sym : forall s1 s2 : set, inter s1 s2 = inter s2 s1.
Axiom
  inter_assoc :
    forall s1 s2 s3 : set, inter s1 (inter s2 s3) = inter (inter s1 s2) s3.

Axiom
  wf_inter :
    forall s1 s2 : set,
    wf s1 = true -> wf s2 = true -> wf (inter s1 s2) = true.
Axiom card_interL : forall s1 s2 : set, (card (inter s1 s2) <= card s1)%Z.
Axiom card_interR : forall s1 s2 : set, (card (inter s1 s2) <= card s2)%Z.

(* ----- diff ------- *)
Axiom
  inter_sem :
    forall (a : A) (s1 s2 : set),
    s_in a s2 = true -> s_in a (diff s1 s2) = false.
Axiom diff_empty : forall s : set, diff s empty = s.
Axiom diff_diff : forall s : set, diff s s = empty.
Axiom diff_inter : forall s1 s2 : set, diff s1 s2 = diff s1 (inter s1 s2).
Axiom
  diff_inter_empty :
    forall s1 s2 : set, inter s1 s2 = empty -> diff s1 s2 = s1.
Axiom
  wf_diff :
    forall s1 s2 : set,
    wf s1 = true -> wf s2 = true -> wf (diff s1 s2) = true.
Axiom card_diff : forall s1 s2 : set, (card (diff s1 s2) <= card s1)%Z.
Axiom
  incl_inter_union :
    forall s1 s2 : set, incl (inter s1 s2) (union s1 s2) = true.



(* ----- union ------- *)
Axiom
  union_semL :
    forall (a : A) (s1 s2 : set),
    s_in a s1 = true -> s_in a (union s1 s2) = true.
Axiom
  union_semR :
    forall (a : A) (s1 s2 : set),
    s_in a s2 = true -> s_in a (union s1 s2) = true.

Axiom union_incl : forall s1 s2 : set, incl s1 s2 = true -> union s1 s2 = s2.
Axiom union_empty : forall s : set, union s empty = s.
Axiom union_empty2 : forall s : set, union empty s = s.
Axiom union_idem : forall s : set, union s s = s.


Axiom
  union_item :
    forall (a : A) (s1 s2 : set),
    union (item a s1) s2 = union (item a empty) (union s1 s2). 



Axiom union_sym : forall s1 s2 : set, union s1 s2 = union s2 s1.



Axiom
  union_assoc :
    forall s1 s2 s3 : set, union s1 (union s2 s3) = union (union s1 s2) s3.





Axiom
  wf_union :
    forall s1 s2 : set,
    wf s1 = true -> wf s2 = true -> wf (union s1 s2) = true.
Axiom
  card_union :
    forall s1 s2 : set, (card (union s1 s2) <= card s1 + card s2)%Z.



(* ---- inclusion ---- *)

Theorem incl_succ :
 forall (a1 : A) (s1 s2 : set),
 incl (item a1 s1) s2 = true -> incl s1 s2 = true.
Proof.
intros.
assert ({s_in a1 s2 = true} + {s_in a1 s2 = false}).
apply in_dec.

elim H0.
intro.
unfold incl in H.
rewrite a in H.
apply H.

intro.
unfold incl in H.
rewrite b in H.
discriminate.
Qed.




Axiom
  in_incl :
    forall s1 s2 : set,
    (forall a : A, s_in a s1 = true -> s_in a s2 = true) <->
    incl s1 s2 = true.

Axiom incl_empty : forall s : set, incl empty s = true.
Axiom incl_empty_not : forall s : set, s <> empty -> incl s empty = false.


Axiom incl_reflexive : forall s : set, incl s s = true.



Section reflexiveSets.

Theorem incl_dec :
 forall s1 s2 : set, {incl s1 s2 = true} + {incl s1 s2 = false}.
Proof.
simple induction s1.
intro.
simpl in |- *.
left.
reflexivity.

intros.
cut ({incl s s2 = true} + {incl s s2 = false}).
cut ({s_in a s2 = true} + {s_in a s2 = false}).
intros.
elim H0.
elim H1.
intros.
left.
unfold incl in |- *.
rewrite a1.
exact a0.

intros.
right.
unfold incl in |- *.
rewrite a0.
assumption.

intros.
right.
unfold incl in |- *.
rewrite b.
reflexivity.

apply in_dec.

apply (H s2).
Qed.

(*Axiom incl_reflexive:(x:set)(incl x x)=true.*)


(* wrong *)
(*Axiom incl_asymmetric:(x,y:set)(incl x y)=false -> (incl y x)=true.*)




Theorem incl_antisymmetric :
 forall x y : set, incl x y = true -> incl y x = true -> x = y.
Proof.
intros.
apply s_eq_struct.
assert (H1 := s_eq_sem x y).
rewrite H1.
rewrite H.
rewrite H0.
compute in |- *.
reflexivity.
Qed.



Axiom
  incl_transitive :
    forall (b : bool) (x y z : set),
    incl x y = b -> incl y z = b -> incl x z = b.
End reflexiveSets.



Theorem incl_add :
 forall (a : A) (s1 s2 : set), incl s1 s2 = true -> incl s1 (add a s2) = true.
Proof.
simple induction s1.
simpl in |- *.
trivial.

intros.
unfold incl in |- *.
cut ({s_in a0 (add a s2) = true} + {s_in a0 (add a s2) = false}).
intros.
elim H1.
intro.
rewrite a1.
apply H.
generalize H0.
apply incl_succ.

intro.
rewrite b.
cut ({A_eq a a0 = true} + {A_eq a a0 = false}).
intro.
elim H2.
intro.
assert (a = a0).
apply theorder.eq_eq.
assumption.

rewrite H3 in b.
assert (HC := in_add2 a0 s2).
rewrite HC in b.
discriminate.

intro.
simpl in H0.
assert (s_in a0 s2 = false).
generalize b.
apply nin_add.

rewrite H3 in H0.
discriminate.

apply theorder.eq_dec.

apply in_dec.
Qed.



Theorem incl_unionR : forall s1 s2 : set, incl s2 (union s1 s2) = true.
Proof.
simple induction s2.
simpl in |- *.
reflexivity.

intros.
simpl in |- *.
cut (s_in a (add a (union s1 s)) = true).
intro.
rewrite H0.
apply incl_add.
assumption.

apply in_add2.
Qed.

Theorem incl_unionL : forall s1 s2 : set, incl s1 (union s1 s2) = true.
Proof.
intros.
assert (union s1 s2 = union s2 s1).
apply union_sym.

rewrite H.
apply incl_unionR.
Qed.











Theorem incl_incl_unionR :
 forall s s1 s2 : set, incl s s2 = true -> incl s (union s1 s2) = true.
Proof.
simple induction s.
simpl in |- *.
intros; assumption.

intros.
assert ({s_in a s2 = true} + {s_in a s2 = false}).
apply in_dec.

assert ({incl s0 s2 = true} + {incl s0 s2 = false}).
apply incl_dec.

elim H1.
intro.
elim H2.
intro.
unfold incl in |- *.
assert (s_in a (union s1 s2) = true).
apply in_unionR.
exact a0.

rewrite H3.
apply H.
exact a1.

intro.
assert (incl s0 s2 = true).
generalize H0.
apply incl_succ.

rewrite b in H3.
discriminate.

intro.
unfold incl in H0.
rewrite b in H0.
discriminate.
Qed.




Theorem incl_incl_unionL :
 forall s s1 s2 : set, incl s s2 = true -> incl s (union s2 s1) = true.
Proof.
intros.
rewrite union_sym.
apply incl_incl_unionR.
apply H.
Qed.




Axiom
  incl_add_union :
    forall (s1 s2 : set) (a : A),
    incl s1 s2 = true -> incl (add a s1) (add a s2) = true.

(*
Proof
Induction s1.
Intros.
Simpl.
Assert (s_in a (add a s2))=true.
Apply in_add2.

Rewrite -> H0.
Reflexivity.

Intros.
Simpl.
Cut {(A_le a a0)=true}+{(A_le a a0)=false}.
Cut {(A_le a0 a)=true}+{(A_le a0 a)=false}.
Intros.
Elim H1.
Elim H2.
Intros.
Rewrite -> a1.
Rewrite -> a2.
Assert a=a0.
Apply theorder.le_antisymmetric.
Assumption.

Assumption.

Rewrite <- H3.
Apply incl_add.
Apply H0.

Intros.
Rewrite -> b.
Simpl.
Assert (s_in a0 (add a0 s2))=true.
Apply in_add2.

Rewrite -> H3.
Abort.

*)



Theorem incl_union_unionR :
 forall s s1 s2 : set,
 incl s1 s2 = true -> incl (union s1 s) (union s2 s) = true.
Proof.
simple induction s.
intros.
simpl in |- *.
exact H.

intros.
simpl in |- *.
apply incl_add_union.
apply H.
exact H0.
Qed.


Theorem incl_union_union :
 forall s s1 s2 : set,
 incl s1 s2 = true -> incl (union s s1) (union s s2) = true.
Proof.
intros.
assert (union s s1 = union s1 s).
apply union_sym.

assert (union s s2 = union s2 s).
apply union_sym.

rewrite H0; rewrite H1.
apply incl_union_unionR.
apply H.
Qed.



(* ----- wf ------- *)




Axiom
  wf_cat :
    forall s1 s2 : set,
    wf s1 = true ->
    wf s2 = true ->
    forall (s11 s22 : set) (a b : A),
    s1 = cat s11 (item a empty) ->
    s2 = item b s22 -> A_lt a b = true -> wf (cat s1 s2) = true.



Axiom wf_emb : forall (a : A) (s : set), wf (item a s) = true -> wf s = true.
(*Lemma wf_emb:(a:A;s:set) (wf (item a s))=true -> (wf s)=true.
Proof.
Intros a s H.
Elim H.

Intro H1; Intro H2; Elim H2.
Intro H3; Intro H4.
Unfold wf.
Exact H3.
Qed.
*)

Axiom
  wf_in_lt :
    forall (a : A) (s : set),
    wf (item a s) = true -> forall b : A, s_in b s = true -> A_lt a b = true.
(*
Proof.
Induction s;[
  Intros wf b H;Contradiction
| 
  Intros a0 s0 Hind H b H1;
  Assert HH:=(wf_emb a (item a0 s0) H);
  Cut (A_eq b a0)=true \/ (A_lt a0 b)=true;[
    Intro H2;Elim H2;[
	Intro H3
    |

    ]
  |
    ...
  ]
].
Qed.
*)




































(* ---- product ---- *)

Axiom product_empty : forall f : A -> set, product empty f = empty.

Axiom product_empty2 : forall s : set, product s (fun a : A => empty) = empty.

Axiom
  product_single : forall (f : A -> set) (a : A), product (single a) f = f a.


(* -- on les a tous-- *)

Theorem product_sem :
 forall (f : A -> set) (a : A) (s : set),
 s_in a s = true -> incl (f a) (product s f) = true.
Proof.
simple induction s.
simpl in |- *.
intro.
discriminate.

intros.
simpl in |- *.
cut ({A_eq a a0 = true} + {A_eq a a0 = false}).
intros.
elim H1.
intro H'.
assert (H2 : a = a0).
apply theorder.eq_eq.
assumption.

rewrite H2.
apply incl_unionL.

intros.
apply incl_incl_unionR.
apply H.
generalize H0.
apply in_succ.
exact b.

apply theorder.eq_dec.
Qed.


(* -- manque la réciproque -- *)


Axiom product_sem2 :
 forall (f : A -> set) (a : A) (s : set),
 (product (item a s) f) = union (f a) (product s f).





Theorem incl_pa_up :
 forall (f : A -> set) (a : A) (s : set),
 incl (product (add a s) f) (union (f a) (product s f)) = true.
Proof.
simple induction s.
simpl in |- *.
apply incl_reflexive.

intros.
simpl in |- *.
cut ({A_le a0 a = true} + {A_le a0 a = false}).
cut ({A_le a a0 = true} + {A_le a a0 = false}).
intros.
elim H0.
elim H1.
intros.
rewrite a1.
rewrite a2.
simpl in |- *.
assert (HE := union_sym (f a) (union (f a0) (product s0 f))).
rewrite HE.
assert (HA := union_assoc).
rewrite <- HA.
apply incl_union_union.
apply incl_unionL.

intros.
rewrite b.
simpl in |- *.
apply incl_union_union.
apply incl_reflexive.

elim H1.
intros.
rewrite a1.
rewrite b.
simpl in |- *.
assert (HE := union_sym (f a) (union (f a0) (product s0 f))).
rewrite HE.
assert (HA := union_assoc).
rewrite <- HA.
apply incl_union_union.
rewrite union_sym.
apply H.

intros.
rewrite b.
simpl in |- *.
apply incl_union_union; apply incl_reflexive.

apply theorder.le_dec.

apply theorder.le_dec.

Qed.




Theorem incl_up_pa :
 forall (f : A -> set) (a : A) (s : set),
 incl (union (f a) (product s f)) (product (add a s) f) = true.
Proof.
simple induction s.
simpl in |- *.
apply incl_reflexive.

intros.
simpl in |- *.
cut ({A_le a0 a = true} + {A_le a0 a = false}).
cut ({A_le a a0 = true} + {A_le a a0 = false}).
intros.
elim H0.
elim H1.
intros.
rewrite a1.
rewrite a2.
simpl in |- *.
assert (a = a0).
apply theorder.le_antisymmetric.
unfold A_le in a2.
unfold A_le in a1.
assumption.

assumption.

rewrite H2.
rewrite union_assoc.
rewrite union_idem.
apply incl_reflexive.

intros.
rewrite a1.
rewrite b.
simpl in |- *.
apply incl_union_union.
apply incl_reflexive.

elim H1; intros.
rewrite a1; rewrite b; simpl in |- *.
rewrite union_sym.
rewrite <- union_assoc.
apply incl_union_union.
rewrite union_sym.
apply H.

rewrite b.
simpl in |- *.
apply incl_union_union.
apply incl_reflexive.

apply theorder.le_dec.

apply theorder.le_dec.
Qed.





Theorem product_add :
 forall (f : A -> set) (a : A) (s : set),
 product (add a s) f = union (f a) (product s f).
Proof.
intros.
apply incl_antisymmetric.
apply incl_pa_up.

apply incl_up_pa.
Qed.




Theorem incl_pu_up :
 forall (f : A -> set) (s1 s2 : set),
 incl (product (union s1 s2) f) (union (product s1 f) (product s2 f)) = true.
Proof.
simple induction s2.
simpl in |- *.
apply incl_reflexive.

intros a0 s Hrec.
simpl in |- *.
assert (H := product_add f a0 (union s1 s)).
rewrite H.
clear H.
assert (H := union_sym (product s1 f) (union (f a0) (product s f))).
rewrite H.
clear H.
assert (H := union_assoc (f a0) (product s f) (product s1 f)).
rewrite <- H.
apply incl_union_union.
clear H.
assert (H := union_sym (product s f) (product s1 f)).
rewrite H; clear H.
apply Hrec.
Qed.




Theorem incl_up_pu :
 forall (f : A -> set) (s1 s2 : set),
 incl (union (product s1 f) (product s2 f)) (product (union s1 s2) f) = true.
Proof.
simple induction s2.
simpl in |- *.
apply incl_reflexive.

intros.
simpl in |- *.
rewrite union_sym.
rewrite <- union_assoc.
rewrite product_add.
apply incl_union_union.
rewrite union_sym.
apply H.
Qed.






Theorem product_unionL :
 forall (f : A -> set) (s1 s2 : set),
 product (union s1 s2) f = union (product s1 f) (product s2 f).
Proof.
intros.
apply incl_antisymmetric.
apply incl_pu_up.
apply incl_up_pu.
Qed.






Theorem incl_puR_up :
 forall (f1 f2 : A -> set) (s : set),
 incl (product s (fun x : A => union (f1 x) (f2 x)))
   (union (product s f1) (product s f2)) = true.
Proof.
simple induction s.
simpl in |- *.
reflexivity.

intros.
simpl in |- *.
rewrite <- union_assoc.
rewrite <- union_assoc.
apply incl_union_union.
assert (H2 := union_sym (product s0 f1) (union (f2 a) (product s0 f2))).
rewrite H2.
rewrite <- union_assoc.
apply incl_union_union.
clear H2.
assert (H3 := union_sym (product s0 f2) (product s0 f1)).
rewrite H3.
apply H.
Qed.



Theorem incl_up_puR :
 forall (f1 f2 : A -> set) (s : set),
 incl (union (product s f1) (product s f2))
   (product s (fun x : A => union (f1 x) (f2 x))) = true.
Proof.
simple induction s.
simpl in |- *.
reflexivity.

intros.
simpl in |- *.
rewrite <- union_assoc.
assert (H4 := union_sym (product s0 f1) (union (f2 a) (product s0 f2))).
rewrite H4.
rewrite union_assoc.
rewrite union_assoc.
rewrite <- union_assoc.
apply incl_union_union.
clear H4.
rewrite union_sym.
apply H.
Qed.






Theorem product_unionR :
 forall (f1 f2 : A -> set) (s : set),
 product s (fun x : A => union (f1 x) (f2 x)) =
 union (product s f1) (product s f2).
Proof.
intros.
apply incl_antisymmetric.
apply incl_puR_up.
apply incl_up_puR.
Qed.


(*


Theorem product_associativity: 
	(s:set)(f:A->set)(a:A) 
	((product (product s f) f))=true

bad...


transitivity?


*)







	
	
	
Axiom
  wf_product :
    forall (f : A -> set) (s : set),
    wf s = true -> (forall a : A, wf (f a) = true) -> wf (product s f) = true. 




(* ---- filter ---- *)

Axiom
  filter_sem1 :
    forall (f : A -> bool) (s : set) (a : A),
    s_in a s = true -> f a = true -> s_in a (filter s f) = true.  

Axiom
  filter_sem2 :
    forall (f : A -> bool) (s : set) (a : A),
    s_in a s = true -> f a = false -> s_in a (filter s f) = false.  


(* used *)
Axiom filter_sem3: 
    forall (f : A -> bool),
    filter empty f = empty.
       
(* used *)
Axiom filter_sem4:
    forall (f : A -> bool) (s : set) (a : A),
    filter (item a s) f = if (f a) then (item a (filter s f)) else (filter s f).



Axiom filter_sem5:
    forall (f : A -> bool) (s : set) (a : A),
    (f a=true)->s_in a (filter (item a s) f) = true.
    
Axiom filter_sem6:
    forall (f : A -> bool) (s : set) (a : A),
    (f a=false)->s_in a (filter (item a s) f) = false.






Axiom
  wf_filter :
    forall (f : A -> bool) (s : set), wf s = true -> wf (filter s f) = true. 













End geneSets.


Module SetOrder (M: genSetsInt) : PartialReflexiveOrder.

Definition A := M.set.
Definition A_le := M.incl.
Definition dec := M.incl_dec.
Definition reflexive := M.incl_reflexive.
Definition antisymmetric := M.incl_antisymmetric.
Definition transitive := M.incl_transitive.

End SetOrder.

Module SetDecidableEq (M: genSetsInt) : DecidableEquality with Definition
  A := M.set.

Definition A := M.set.
Definition A_eq := M.s_eq.
Definition dec := M.s_eq_dec.
Definition reflexive := M.s_eq_reflexive.
Definition symmetric := M.s_eq_symmetric.
Definition transitive := M.s_eq_transitive.
Definition eq_struct := M.s_eq_struct.

End SetDecidableEq.
