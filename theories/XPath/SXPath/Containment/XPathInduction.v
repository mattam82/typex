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


(* Default Induction Scheme

Check XPath_ind
:
(P:(XPath->Prop))
 (P void)
 ->(P top)
 ->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (union x x0)))
 ->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (slash x x0)))
 ->((x:XPath)(P x)->(x0:XQualif)(P (qualif x x0)))
 ->((a:Axis; n:NodeTest)(P (step a n)))
 ->(x:XPath)(P x)
*)



(* generation of mutual induction schemes...Coq I love you !!! *)
Scheme XJ1 := Induction for XPath Sort Prop
  with XJ2 := Induction for XQualif Sort Prop.


(*
Check XJ1 
:
(P:(XPath->Prop); P0:(XQualif->Prop))
   (P void)
 ->(P top)
 ->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (union x x0)))
 ->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (slash x x0)))
 ->((x:XPath)
    (P x)->(x0:XQualif)(P0 x0)->(P (qualif x x0)))
 ->((a:Axis; n:NodeTest)(P (step a n)))
 ->((x:XQualif)(P0 x)->(P0 (not x)))
 ->((x:XQualif)
    (P0 x)
    ->(x0:XQualif)(P0 x0)->(P0 (and x x0)))
 ->((x:XQualif)
    (P0 x)
    ->(x0:XQualif)(P0 x0)->(P0 (or x x0)))
 ->((x:XPath)
    (P x)
    ->(x0:XPath)(P x0)->(P0 (leq x x0)))
 ->(P0 _true)
 ->(P0 _false)
 ->(x:XPath)(P x)

Check XJ2

: (P:(XPath->Prop); P0:(XQualif->Prop))
  (P void)
->(P top)
->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (union x x0)))
->((x:XPath)(P x)->(x0:XPath)(P x0)->(P (slash x x0)))
->((x:XPath)
   (P x)->(x0:XQualif)(P0 x0)->(P (qualif x x0)))
->((a:Axis; n:NodeTest)(P (step a n)))
->((x:XQualif)(P0 x)->(P0 (not x)))
->((x:XQualif)
   (P0 x) ->(x0:XQualif)(P0 x0)->(P0 (and x x0)))
->((x:XQualif)
   (P0 x) ->(x0:XQualif)(P0 x0)->(P0 (or x x0)))
->((x:XPath)
   (P x) ->(x0:XPath)(P x0)->(P0 (leq x x0)))
->(P0 _true)
->(P0 _false)
->(x:XQualif)(P0 x)
*)

(*

(* A double Mutual Induction Scheme *)
Lemma DInd:
(P:(XPath->XPath->Prop); P0:(XQualif->XQualif->Prop))
  ((x:XPath)(P void x) )
->((x:XPath)(P x void) )
->((x:XPath)(P top x))
->((x:XPath)(P x top))

->((x,xp,x2:XPath)(P x xp)->(x0,x0p:XPath)(P x0 x0p)->(P (union x x0) x2))
->((x,xp,x2:XPath)(P xp x)->(x0,x0p:XPath)(P x0p x0)->(P x2 (union x x0)))

->((x,xp,x2:XPath)(P x xp)->(x0,x0p:XPath)(P x0 x0p)->(P (slash x x0) x2))
->((x,xp,x2:XPath)(P xp x)->(x0,x0p:XPath)(P x0p x0)->(P x2 (slash x x0)))

->((x,xp,x2:XPath)
  (P x xp)->(x0,x0p:XQualif)(P0 x0 x0p)->(P (qualif x x0) x2))
->((x,xp,x2:XPath)
  (P xp x)->(x0,x0p:XQualif)(P0 x0p x0)->(P x2 (qualif x x0)))

->((a:Axis; n:NodeTest;x:XPath)(P (step a n) x))
->((a:Axis; n:NodeTest;x:XPath)(P x (step a n)))


->((x,xp,x2:XQualif)(P0 x xp)->(P0 (not x) x2))
->((x,xp,x2:XQualif)(P0 xp x)->(P0 x2 (not x)))

->((x,xp,x2:XQualif)
  (P0 x xp) ->(x0,x0p:XQualif)(P0 x0 x0p)->(P0 (and x x0) x2))
->((x,xp,x2:XQualif)
  (P0 xp x) ->(x0,x0p:XQualif)(P0 x0p x0)->(P0 x2 (and x x0)))

->((x,xp,x2:XQualif)
  (P0 x xp) ->(x0,x0p:XQualif)(P0 x0 x0p)->(P0 (or x x0) x2))
->((x,xp,x2:XQualif)
  (P0 xp x) ->(x0,x0p:XQualif)(P0 x0p x0)->(P0 x2 (or x x0)))

->((x,xp:XPath;y:XQualif)
  (P x xp)->(x0,x0p:XPath)(P x0 x0p)->(P0 (leq x x0) y))

->((x,xp:XPath;y:XQualif)
  (P xp x) ->(x0,x0p:XPath)(P x0p x0)->(P0 y (leq x x0)))

->((x:XQualif)(P0 _true x))
->((x:XQualif)(P0 x _true))
->((x:XQualif)(P0 _false x))
->((x:XQualif)(P0 x _false))
->(x,y:XPath)(P x y).

Proof.
Intros.
Elim x using XJ1 with P0:=[y1:XQualif](y2:XQualif)(P0 y1 y2);Auto.
Intros; Apply H5 with xp:=y x0p:=y;Auto.
Intros; Apply H7 with xp:=y x0p:=y;Auto.
Intros; Apply H9 with xp:=y x0p:=y;Auto.
Intros;Apply H11 with xp:=y x0p:=x1;Auto.
Intros;Apply H15 with xp:=y2;Auto.
Intros;Apply H17 with xp:=y2 x0p:=y2;Auto.
Intros; Apply H19 with xp:=y2 x0p:=y2;Auto.
Intros; Apply H21 with xp:=y x0p:=y;Auto.
Qed.
*)

(* this defines a mesure of structural complexity *)

Require Export Max.
Require Export Le.


Fixpoint CXP (p : XPath) : nat :=
  match p with
  | void => 0
  | top => 0
  | step a n => 1
  | slash p1 p2 => S (max (CXP p1) (CXP p2))
  | union p1 p2 => S (max (CXP p1) (CXP p2))
  | inter p1 p2 => S (max (CXP p1) (CXP p2))
  | qualif p1 q2 => S (max (CXP p1) (CXQ q2))
  end
 
 with CXQ (q : XQualif) : nat :=
  match q with
  | _false => 0
  | _true => 0
  | not q1 => S (CXQ q1)
  | and q1 q2 => S (max (CXQ q1) (CXQ q2))
  | or q1 q2 => S (max (CXQ q1) (CXQ q2))
  | leq p1 p2 => S (max (CXP p1) (CXP p2))
  end.


Definition BasicInd (hyp : nat -> Prop) : Prop :=
  hyp 0 -> (forall i : nat, hyp i -> hyp (S i)) -> forall n : nat, hyp n.

Definition BasicInd_rec (hyp : nat -> Set) : Set :=
  hyp 0 -> (forall i : nat, hyp i -> hyp (S i)) -> forall n : nat, hyp n.


Definition BasicDoubleInd (hyp : nat -> Prop) : Prop :=
  hyp 0 ->
  hyp 1 ->
  (forall i : nat, hyp (S i) -> hyp (S (S i)) -> hyp (S (S (S i)))) ->
  forall n : nat, hyp n.


Definition Hyp22 (P : XPath -> XPath -> Prop)
  (Q : XQualif -> XQualif -> Prop) (i : nat) : Prop :=
  (forall p1 p2 : XPath, max (CXP p1) (CXP p2) <= i -> P p1 p2) /\
  (forall q1 q2 : XQualif, max (CXQ q1) (CXQ q2) <= i -> Q q1 q2).

Definition Hyp22_rec (P : XPath -> XPath -> Set)
  (Q : XQualif -> XQualif -> Set) (i : nat) : Set :=
  ((forall p1 p2 : XPath, max (CXP p1) (CXP p2) <= i -> P p1 p2) *
   (forall q1 q2 : XQualif, max (CXQ q1) (CXQ q2) <= i -> Q q1 q2))%type.


Lemma HInd22 :
 forall (P : XPath -> XPath -> Prop) (Q : XQualif -> XQualif -> Prop),
 BasicInd (Hyp22 P Q).
intros P Q.
unfold BasicInd in |- *.
intros H0 Hi.
simple induction n; [ auto | intro n0; apply (Hi n0); trivial ].
Qed.

Lemma HInd22_rec :
 forall (P : XPath -> XPath -> Set) (Q : XQualif -> XQualif -> Set),
 BasicInd_rec (Hyp22_rec P Q).
intros P Q.
unfold BasicInd_rec in |- *.
intros H0 Hi.
simple induction n; [ auto | intro n0; apply (Hi n0); trivial ].
Qed.





Lemma Hyp_sound : forall p : XPath, exists i : nat, CXP p = i.
simple induction p.
exists 0; trivial.

exists 0; trivial.

intros x H0 x0 H1.
simpl in |- *; exists (S (max (CXP x) (CXP x0))); trivial.

intros x H0 x0 H1.
simpl in |- *; exists (S (max (CXP x) (CXP x0))); trivial.

intros x H0 x0 H1.
simpl in |- *; exists (S (max (CXP x) (CXP x0))); trivial.

intros x H0 x0.
simpl in |- *; exists (S (max (CXP x) (CXQ x0))); trivial.

intros; simpl in |- *; exists 1; trivial.

Qed.


Lemma HGen22 :
 forall (P : XPath -> XPath -> Prop) (Q : XQualif -> XQualif -> Prop),
 (forall n : nat, Hyp22 P Q n) ->
 (forall p1 p2 : XPath, P p1 p2) /\ (forall q1 q2 : XQualif, Q q1 q2).
intros.
unfold Hyp22 in H.
split.

intros p1 p2; elim (H (max (CXP p1) (CXP p2))).
intros H0 H1; apply H0.
auto.

intros q1 q2; elim (H (max (CXQ q1) (CXQ q2))).
intros H0 H1; apply H1.
auto.
Qed.

Lemma HGen22_rec :
 forall (P : XPath -> XPath -> Set) (Q : XQualif -> XQualif -> Set),
 (forall n : nat, Hyp22_rec P Q n) ->
 (forall p1 p2 : XPath, P p1 p2) * (forall q1 q2 : XQualif, Q q1 q2).
intros.
unfold Hyp22_rec in H.
split.

intros p1 p2; elim (H (max (CXP p1) (CXP p2))).
intros H0 H1; apply H0.
auto.

intros q1 q2; elim (H (max (CXQ q1) (CXQ q2))).
intros H0 H1; apply H1.
auto.
Qed.


Definition Hyp11 (P : XPath -> Prop)
  (Q : XQualif -> Prop) (i : nat) : Prop :=
  (forall p : XPath, (CXP p) <= i -> P p) /\
  (forall q : XQualif, (CXQ q) <= i -> Q q).


Lemma HInd11 :
 forall (P : XPath -> Prop) (Q : XQualif -> Prop),
 BasicInd (Hyp11 P Q).
intros P Q.
unfold BasicInd in |- *.
intros H0 Hi.
simple induction n; [ auto | intro n0; apply (Hi n0); trivial ].
Qed.


Lemma HGen11 :
 forall (P : XPath -> Prop) (Q : XQualif -> Prop),
 (forall n : nat, Hyp11 P Q n) ->
 (forall p : XPath, P p) /\ (forall q : XQualif, Q q).
intros.
unfold Hyp11 in H.
split.

intros p; elim (H (CXP p)).
intros H0 H1; apply H0.
auto.

intros q; elim (H (CXQ q)).
intros H0 H1; apply H1.
auto.
Qed.

Definition Hyp2222plus 
	(P PE: XPath -> XPath -> Prop)
	(Q QE : XQualif -> XQualif -> Prop) 
	(i : nat) 
	: Prop :=
  (forall p1 p2 : XPath, plus (CXP p1) (CXP p2) <= i -> P p1 p2) /\
  (forall p1 p2 : XPath, plus (CXP p1) (CXP p2) <= i -> PE p1 p2) /\
  (forall q1 q2 : XQualif, plus (CXQ q1) (CXQ q2) <= i -> Q q1 q2) /\
  (forall q1 q2 : XQualif, plus (CXQ q1) (CXQ q2) <= i -> QE q1 q2).

Lemma HInd2222plus :
 forall (P PE : XPath -> XPath -> Prop) (Q QE: XQualif -> XQualif -> Prop),
 BasicInd (Hyp2222plus P PE Q QE).
intros P PE Q QE.
unfold BasicInd in |- *.
intros H0 Hi.
simple induction n; [ auto | intro n0; apply (Hi n0); trivial ].
Qed.

Lemma HGen2222plus :
 forall (P PE: XPath -> XPath -> Prop) (Q QE: XQualif -> XQualif -> Prop),
 (forall n : nat, Hyp2222plus P PE Q QE n) ->
 (forall p1 p2 : XPath, P p1 p2) /\ 
 (forall p1 p2 : XPath, PE p1 p2) /\ 
 (forall q1 q2 : XQualif, Q q1 q2) /\
 (forall q1 q2 : XQualif, QE q1 q2)
.
intros.
unfold Hyp2222plus in H.
split.

intros p1 p2; elim (H (plus (CXP p1) (CXP p2))).
intros H0 _; apply H0.
auto with arith.

split.
intros p1 p2; elim (H (plus (CXP p1) (CXP p2))).
intros _ [H0 [H1 H2]]; apply H0.
auto with arith.

split.
intros q1 q2; elim (H (plus (CXQ q1) (CXQ q2))).
intros _ [H0 [H1 H2]]; apply H1.
auto with arith.

intros q1 q2; elim (H (plus (CXQ q1) (CXQ q2))).
intros _ [H0 [H1 H2]]; apply H2.
auto with arith.
Qed.
