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

Module Type genSetsInt.

Parameter A : Set.
Parameter A_le : A -> A -> bool.
Parameter A_lt : A -> A -> bool.
Parameter A_eq : A -> A -> bool.
(*
Parameter set:Set.
Parameter empty:set.
Parameter item:A->set->set.
*)
Inductive set : Set :=
  | empty : set
  | item : A -> set -> set.
Parameter single : A -> set.
Parameter s_in : A -> set -> bool.
Parameter cat : set -> set -> set.
Parameter wf : set -> bool.
Parameter card : set -> Z.

Parameter add : A -> set -> set.
Parameter sub : A -> set -> set.

Parameter reduce : forall B : Set, (B -> A -> B) -> B -> set -> B.

Parameter union : set -> set -> set.
Parameter inter : set -> set -> set.
Parameter diff : set -> set -> set.

Parameter incl : set -> set -> bool.
Parameter s_eq : set -> set -> bool.

Parameter product : set -> (A -> set) -> set.
Parameter filter : set -> (A -> bool) -> set.



Axiom not_single_empty : forall x : A, single x <> empty.

Axiom
  wf_cat :
    forall s1 s2 : set,
    wf s1 = true ->
    wf s2 = true ->
    forall (s11 s22 : set) (a b : A),
    s1 = cat s11 (item a empty) ->
    s2 = item b s22 -> A_lt a b = true -> wf (cat s1 s2) = true.
	
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

Axiom in_sem1 : forall a : A, s_in a empty = false.
Axiom in_sem2 : forall (a : A) (s : set), s_in a (item a s) = true.
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


Axiom single_sem : forall x : A, s_in x (single x) = true.
Axiom in_single : forall x y : A, s_in x (single y) = true -> x=y.

Axiom
  in_dec : forall (s : set) (a : A), {s_in a s = true} + {s_in a s = false}.

Axiom wf_emb : forall (a : A) (s : set), wf (item a s) = true -> wf s = true.
Axiom
  wf_in_lt :
    forall (a : A) (s : set),
    wf (item a s) = true -> forall b : A, s_in b s = true -> A_lt a b = true.
Axiom
  in_embedded :
    forall (a b : A) (s : set), s_in a s = true -> s_in a (item b s) = true.

(* ----- cardinal ---- *)
Axiom card_is_pos : forall s : set, (0 <= card s)%Z.
Axiom card_empty : card empty = 0%Z.

(* ----- add ------- *)
Axiom add_sem1 : forall (a : A) (s : set), s_in a s = true -> add a s = s.
Axiom add_sem2 : forall (a : A) (s : set), s_in a (add a s) = true.
Axiom
  in_add :
    forall (a : A) (s : set),
    s_in a s = true -> forall b : A, s_in a (add b s) = true.
Axiom add_wf : forall (a : A) (s : set), wf s = true -> wf (add a s) = true.
Axiom
  add_card1 :
    forall (a : A) (s : set),
    s_in a s = false -> card (add a s) = (card s + 1)%Z.
Axiom add_card2 : forall (a : A) (s : set), (card (add a s) >= card s)%Z.

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

(* ----- union ------- *)
Axiom
  union_semL :
    forall (a : A) (s1 s2 : set),
    s_in a s1 = true -> s_in a (union s1 s2) = true.
Axiom
  union_semR :
    forall (a : A) (s1 s2 : set),
    s_in a s2 = true -> s_in a (union s1 s2) = true.

Axiom incl_unionR : forall s1 s2 : set, incl s2 (union s1 s2) = true.
Axiom incl_unionL : forall s1 s2 : set, incl s1 (union s1 s2) = true.
Axiom
  incl_incl_unionR :
    forall s s1 s2 : set, incl s s2 = true -> incl s (union s1 s2) = true.
Axiom
  incl_incl_unionL :
    forall s s1 s2 : set, incl s s2 = true -> incl s (union s2 s1) = true.

Axiom union_incl : forall s1 s2 : set, incl s1 s2 = true -> union s1 s2 = s2.
Axiom union_empty : forall s : set, union s empty = s.
Axiom union_empty2 : forall s : set, union empty s = s.
Axiom union_idem : forall s : set, union s s = s.
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

(* ---- mixing operators ---- *)
(*
Axiom inter_union: (s1,s2:set) (inter s1 (union s2 s3))=(union (inter s1 s2) (inter s1 s3)).
Axiom inter_diff: (s1,s2:set) (inter s1 (diff s2 s3))=(diff (inter s1 s2) s3).

Axiom union_inter: (s1,s2:set) (union s1 (inter s2 s3))=(inter (union s1 s2) (union s1 s3)).
Axiom union_diff: (s1,s2:set) (union s1 (diff s2 s3))=(union (diff (union s1 s2) s3) (diff (inter s1 s3) s2)).

Axiom diff_union1: (s1,s2:set) (diff s1 (union s2 s3))=(union (diff s1 s2) (diff s1 s3)).
Axiom diff_union2: (s1,s2:set) (diff s1 (union s2 s3))=(diff (diff s1 s2) s3).
Axiom diff_inter: (s1,s2:set) (diff s1 (inter s2 s3))=(inter (diff s1 s2) (diff s1 s3)).

All: To be checked !

*)
 

(* ---- inclusion ---- *)
Axiom
  in_incl :
    forall s1 s2 : set,
    (forall a : A, s_in a s1 = true -> s_in a s2 = true) <->
    incl s1 s2 = true.

Axiom incl_empty : forall s : set, incl empty s = true.
Axiom incl_empty_not : forall s : set, s <> empty -> incl s empty = false.

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
 

(* ---- product ---- *)
Axiom
  product_sem :
    forall (f : A -> set) (a : A) (s : set),
    s_in a s = true -> incl (f a) (product s f) = true.
Axiom
  wf_product :
    forall (f : A -> set) (s : set),
    wf s = true -> (forall a : A, wf (f a) = true) -> wf (product s f) = true. 

Axiom
  product_single : forall (f : A -> set) (a : A), product (single a) f = f a.


Axiom product_sem2 :
 forall (f : A -> set) (a : A) (s : set),
 (product (item a s) f) = union (f a) (product s f).


Axiom
  product_unionL :
    forall (f : A -> set) (s1 s2 : set),
    product (union s1 s2) f = union (product s1 f) (product s2 f).

Axiom
  product_unionR :
    forall (f1 f2 : A -> set) (s : set),
    product s (fun x : A => union (f1 x) (f2 x)) =
    union (product s f1) (product s f2).

Axiom product_empty : forall f : A -> set, product empty f = empty.

Axiom product_empty2 : forall s : set, product s (fun a : A => empty) = empty.

Axiom product_add :
 forall (f : A -> set) (a : A) (s : set),
 product (add a s) f = union (f a) (product s f).


(* ---- filter ---- *)
Axiom
  filter_sem1 :
    forall (f : A -> bool) (s : set) (a : A),
    s_in a s = true -> f a = true -> s_in a (filter s f) = true.  
Axiom
  filter_sem2 :
    forall (f : A -> bool) (s : set) (a : A),
    s_in a s = true -> f a = false -> s_in a (filter s f) = false.  
    

Axiom filter_sem3: 
    forall (f : A -> bool),
    filter empty f = empty.
    
    
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

(*
Axiom incl_sem: (x,y:set) ( (a:A)(s_in a x)=true -> (s_in a y)=true ) -> (incl x y)=true.

Axiom product_sem2:
	(f:A->set ; s:set; x:A)
	(s_in x s)=true -> (product s f)= (union (f x) (product (sub x s) f)
	.
Axiom product_sem4:
	(f:A->set ; s:set)
	s=empty -> (product s f)=empty
	.
*)


Section reflexiveSets.
Axiom incl_dec : forall x y : set, {incl x y = true} + {incl x y = false}.
Axiom incl_reflexive : forall x : set, incl x x = true.

(* wrong *)
(*Axiom incl_asymmetric:(x,y:set)(incl x y)=false -> (incl y x)=true.*)

Axiom
  incl_antisymmetric :
    forall x y : set, incl x y = true -> incl y x = true -> x = y.
Axiom
  incl_transitive :
    forall (b : bool) (x y z : set),
    incl x y = b -> incl y z = b -> incl x z = b.
End reflexiveSets.




End genSetsInt.