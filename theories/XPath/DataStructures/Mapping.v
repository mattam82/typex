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
Require Import setOrder.


Module Type MappingInt.

  Parameter A B : Set.

  (* ----- strict order on type A ---- *)
  Parameter A_lt : A -> A -> bool.
  Parameter A_eq : A -> A -> bool.


  (*----- Definition of the mapping type ----- *)


  Parameter Mapping : Set.
  Parameter empty : Mapping.

  (* (option B) is either (None B) or (b:B)(Some B b) *)
  Definition some := Some (A:=B).
  Definition none := None (A:=B).

  Parameter map_get : A -> Mapping -> option B.
  Parameter map_in : A -> Mapping -> bool.
  Parameter map_add : A * B -> Mapping -> Mapping.
  Parameter map_sub : A -> Mapping -> Mapping.
  Parameter map_incl : Mapping -> Mapping -> bool.
  Parameter map_eq : Mapping -> Mapping -> bool.
  Parameter map_reduce : forall C : Set, C -> (B -> C -> C) -> Mapping -> C.

  Axiom
    get_sem1 :
      forall (a : A) (m : Mapping),
      map_in a m = true <-> (exists b : B, map_get a m = some b).  
  Axiom
    get_sem2 :
      forall (a : A) (m : Mapping), map_in a m = false <-> map_get a m = none.  
  Axiom
    get_sem3 :
      forall (a : A) (m : Mapping) (b : B),
      map_get a m = some b -> exists m' : Mapping, m = map_add (a, b) m'.  
  Axiom get_empty : forall a : A, map_get a empty = none.

  Axiom in_empty : forall a : A, map_in a empty = false.

  (* ---- add operation semantics ---- *)
  Axiom
    add_sem1 :
      forall (a : A) (b : B) (m : Mapping),
      map_in a (map_add (a, b) m) = true.
  Axiom
    add_sem2 :
      forall (a : A) (b : B) (m : Mapping),
      map_get a (map_add (a, b) m) = some b.
  Axiom
    add_sem3 :
      forall (a a' : A) (b : B) (m : Mapping),
      A_eq a a' = false -> map_get a (map_add (a', b) m) = map_get a m.

  (* ---- sub operation semantics --- *)
  Axiom
    sub_sem :
      forall (a : A) (b : B) (m : Mapping), map_sub a (map_add (a, b) m) = m.
  Axiom
    sub_sem1 :
      forall (a : A) (m : Mapping),
      map_in a m = true -> map_in a (map_sub a m) = false.
  Axiom
    sub_sem2 :
      forall (a : A) (m : Mapping), map_in a m = false -> map_sub a m = m.


  Axiom
    map_incl_sem :
      forall (a : A) (m m' : Mapping),
      map_incl m m' = true -> map_get a m = map_get a m'.
  Axiom
    map_eq_sem :
      forall (a : A) (m m' : Mapping),
      map_eq m m' = andb (map_incl m m') (map_incl m' m). 
  Axiom
    map_eq_struct :
      forall (a : A) (m m' : Mapping), map_eq m m' = true <-> m = m'.

  Axiom
    map_reduce_sem_empty :
      forall (C : Set) (init : C) (f : B -> C -> C),
      map_reduce C init f empty = init.

  Axiom
    map_reduce_sem :
      forall (C : Set) (init : C) (f : B -> C -> C) 
        (a : A) (b : B) (m : Mapping),
      (forall (b1 b2 : B) (c : C), f b1 (f b2 c) = f b2 (f b1 c)) ->
      map_reduce C init f (map_add (a, b) m) = f b (map_reduce C init f m).

  Axiom
    map_structure :
      forall m : Mapping,
      {m = empty} +
      {exists a : A,
         (exists b : B, (exists m' : Mapping, m = map_add (a, b) m'))}.

End MappingInt.


Module genMapping (theOrderA: CmpOrderTheory) (theOrderB: DecidableEquality)
  : MappingInt with Definition A := theOrderA.A with Definition
  B := theOrderB.A.


  Definition A := theOrderA.A.
  Definition A_le := theOrderA.le.
  Definition A_lt := theOrderA.lt.
  Definition A_eq := theOrderA.eq.

  Definition B := theOrderB.A.
  Definition B_eq := theOrderB.A_eq.

  (*----- Definition of the mapping type ----- *)

  Inductive mapping : Set :=
    | m_empty : mapping
    | m_item : A * B -> mapping -> mapping.

  Definition Mapping := mapping.
  Definition empty := m_empty.


  Definition some := Some (A:=B).
  Definition none := None (A:=B).



  Fixpoint map_get (a : A) (m : Mapping) {struct m} : 
   option B :=
    match m with
    | m_empty => none
    | m_item (e1, e2) x =>
        if A_le a e1
        then if A_le e1 a then some e2 else map_get a x
        else none
    end.

  Fixpoint map_in (a : A) (x : Mapping) {struct x} : bool :=
    match x with
    | m_empty => false
    | m_item (a1, _) x1 =>
        if A_le a a1 then if A_le a1 a then true else map_in a x1 else false
    end.

  Fixpoint map_wf (x : Mapping) : Prop :=
    match x with
    | m_empty => True
    | m_item (a1, _) x1 =>
        if map_in a1 x1
        then False
        else
         match x1 with
         | m_item (a2, _) x2 => if A_lt a1 a2 then map_wf x1 else False
         | m_empty => True
         end
    end.

  Fixpoint map_add (e : A * B) (x : Mapping) {struct x} : Mapping :=
    match x with
    | m_empty => m_item e m_empty
    | m_item (a1, b1) x1 =>
        match e with
        | (a2, b2) =>
            if A_le a1 a2
            then
             if A_le a2 a1
             then m_item e x1
             else m_item (a1, b1) (map_add e x1)
            else m_item e x
        end
    end.

  Fixpoint map_sub (a : A) (x : Mapping) {struct x} : Mapping :=
    match x with
    | m_empty => x
    | m_item (a1, b1) x1 =>
        if A_le a1 a
        then if A_le a a1 then x1 else m_item (a1, b1) (map_sub a x1)
        else x
    end.

  Fixpoint map_incl (m m' : Mapping) {struct m} : bool :=
    match m with
    | m_empty => true
    | m_item (a, b) m1 =>
        match map_get a m' with
        | Some b' => if B_eq b b' then map_incl m1 m' else false
        | None => false
        end
    end.

  Fixpoint map_eq (m m' : Mapping) {struct m'} : bool :=
    match m, m' with
    | m_empty, m_empty => true
    | m_item (a, b) m1, m_item (a', b') m2 =>
        if A_le a a'
        then
         if A_le a' a
         then if B_eq b b' then map_eq m1 m2 else false
         else false
        else false
    | _, _ => false
    end.

  Fixpoint map_reduce (C : Set) (init : C) (f : B -> C -> C) 
   (m : Mapping) {struct m} : C :=
    match m with
    | m_empty => init
    | m_item (a, b) m' => f b (map_reduce C init f m')
    end.

  (*---- well-formedness ---- *)
  Axiom wf1 : map_wf m_empty.
  Axiom wf2 : forall x : A * B, map_wf (m_item x m_empty).
  Axiom
    wf3 :
      forall (a : A) (b : B) (m : Mapping),
      map_wf m ->
      map_in a m = false ->
      forall (a' : A) (b' : B) (m' : Mapping),
      m = m_item (a', b') m' -> A_lt a a' = true -> map_wf (m_item (a, b) m).

  Axiom
    get_sem1 :
      forall (a : A) (m : Mapping),
      map_in a m = true <-> (exists b : B, map_get a m = some b).  
  Axiom
    get_sem2 :
      forall (a : A) (m : Mapping), map_in a m = false <-> map_get a m = none.  
  Axiom
    get_sem3 :
      forall (a : A) (m : Mapping) (b : B),
      map_get a m = some b -> exists m' : Mapping, m = map_add (a, b) m'.  
  Axiom get_empty : forall a : A, map_get a m_empty = none.

  Axiom in_empty : forall a : A, map_in a m_empty = false.

  (* ---- add operation semantics ---- *)
  Axiom
    add_sem1 :
      forall (a : A) (b : B) (m : Mapping),
      map_in a (map_add (a, b) m) = true.
  Axiom
    add_sem2 :
      forall (a : A) (b : B) (m : Mapping),
      map_get a (map_add (a, b) m) = some b.
  Axiom
    add_sem3 :
      forall (a a' : A) (b : B) (m : Mapping),
      A_eq a a' = false -> map_get a (map_add (a', b) m) = map_get a m.
  Axiom
    add_sem4 :
      forall (a : A) (b1 b2 : B) (m : Mapping),
      map_add (a, b1) (map_add (a, b2) m) = map_add (a, b1) m.
  Axiom
    add_wf :
      forall (x : A * B) (m : Mapping), map_wf m -> map_wf (map_add x m).

  (* ---- sub operation semantics --- *)
  Axiom
    sub_sem :
      forall (a : A) (b : B) (m : Mapping), map_sub a (map_add (a, b) m) = m.
  Axiom
    sub_sem1 :
      forall (a : A) (m : Mapping),
      map_in a m = true -> map_in a (map_sub a m) = false.
  Axiom
    sub_sem2 :
      forall (a : A) (m : Mapping), map_in a m = false -> map_sub a m = m.

  Axiom
    map_incl_sem :
      forall (a : A) (m m' : Mapping),
      map_incl m m' = true -> map_get a m = map_get a m'.
  Axiom
    map_eq_sem :
      forall (a : A) (m m' : Mapping),
      map_eq m m' = andb (map_incl m m') (map_incl m' m). 
  Axiom
    map_eq_struct :
      forall (a : A) (m m' : Mapping), map_eq m m' = true <-> m = m'.

  Axiom
    map_reduce_sem_empty :
      forall (C : Set) (init : C) (f : B -> C -> C),
      map_reduce C init f empty = init.

  Axiom
    map_reduce_sem :
      forall (C : Set) (init : C) (f : B -> C -> C) 
        (a : A) (b : B) (m : Mapping),
      (forall (b1 b2 : B) (c : C), f b1 (f b2 c) = f b2 (f b1 c)) ->
      map_reduce C init f (map_add (a, b) m) = f b (map_reduce C init f m).

  Axiom
    map_structure :
      forall m : Mapping,
      {m = empty} +
      {exists a : A,
         (exists b : B, (exists m' : Mapping, m = map_add (a, b) m'))}.

End genMapping.