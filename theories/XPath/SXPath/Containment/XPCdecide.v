(******************************************************************************
September 2004
Authors: Jean-Yves Vion-dury and Pierre Geneves 

jean-yves.vion-dury@xrce.xerox.com
WAM Research Project, INRIA Rhone-Alpes and Xerox Research Center Europe

pierre.geneves@inrialpes.fr
WAM Research Project, INRIA Rhone-Alpes

Please do not reuse or publish this code without explicit consent from authors.
*******************************************************************************)
Require Import XPequiv.
Require Import XPCAxioms.
Require Import XPathGrammar.

(*
Ltac SolvePEquiv :=
   match goal with
   |  |- (Pequiv ?p (qualif _ _true)) => first [
         apply Pequiv_refl
       | apply Pequiv_sym
       | apply equ_s_union_L;SolvePEquiv
       | apply equ_s_union_R;SolvePEquiv
       ]
   |  |- (Pequiv (union _ _) (union _ _)) => first [
         apply Pequiv_refl
       | apply Pequiv_sym
       | apply equ_s_union_L;SolvePEquiv
       | apply equ_s_union_R;SolvePEquiv
       ]
   |  |- (Pequiv (inter _ _) (inter _ _)) => first [
         apply Pequiv_refl
       | apply Pequiv_sym
       | apply equ_s_inter_L;SolvePEquiv
       | apply equ_s_inter_R;SolvePEquiv
       ]
   |  |- (Pequiv (slash _ _) (slash _ _)) => first [
         apply Pequiv_refl
       | apply Pequiv_sym
       | apply equ_s_slash_L;SolvePEquiv
       | apply equ_s_slash_R;SolvePEquiv
       ]
   end
 with SolveQEquiv :=
   match goal with
   |  |- (Qipl _ (and _ _)) => apply e5; SolveLeQ theTac
   end
.
*)

Ltac SolveLe theTac :=
  unfold dot, star, path, slash2 in |- *;
   match goal with
   |  |- (Ple (union _ _) _) => apply c2c; SolveLe theTac
   |  |- (Ple _ (union _ _)) => first
   [ apply c2a; SolveLe theTac | apply c2b; SolveLe theTac ]
   |  |- (Ple (slash _ _) (step _ _)) => apply g1b; SolveLe theTac
   |  |- (Ple _ (slash top (step descendant _node))) =>
       apply g3b; SolveLe theTac
   |  |- (Ple (slash _ _) (slash top (step descendant _))) =>
       apply g3a; SolveLe theTac
   |  |- (Ple (slash _ _) (slash _ (step _ _))) => 
   apply g1; SolveLe theTac
   |  |- (Ple (slash _ _) (slash _ _)) => first
   [ apply d2a; SolveLe theTac
   | apply d2a; SolveLe theTac
   | apply d2b; SolveLe theTac
   | apply d2c; SolveLe theTac ]
   |  |- (Ple _ _) =>
       (constructor; SolveLe theTac) || solve [ auto ] || (do 1 theTac)
   |  |- (~ Qualif _) => intro _H; inversion _H
   |  |- (Qipl _ _) => SolveLeQ theTac
   |  |- (axis_le _ _) => constructor
   |  |- (head _ <> _) => discriminate || solve [ auto ] || (do 1 theTac)
   |  |- (ntest_le _ _ _) => constructor
   | _ => solve [ auto ]
   end
 with SolveLeQ theTac :=
  unfold dot, star, path, slash2 in |- *;
   match goal with
   |  |- (Qipl _ (_ and _)) => apply e5; SolveLeQ theTac
   |  |- (Qipl (_ and _) _) => first
   [ apply e4a; SolveLeQ theTac | apply e4b; SolveLeQ theTac ]
   |  |- (Qipl (_ or _) _) => apply e7; SolveLeQ theTac
   |  |- (Qipl _ (_ or _)) => first
   [ apply e6a; SolveLeQ theTac | apply e6b; SolveLeQ theTac ]
   |  |- (Qipl _ _) =>
       constructor; SolveLeQ theTac || solve [ auto ] || (do 1 theTac)
   |  |- (Ple _ _) => SolveLe theTac
   | _ => solve [ auto ]
   end.

