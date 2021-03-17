Require Import untypedLC.

(*definition des operateurs booléens*)
Definition ctr:=\x y ~ x.
Definition cfa:=\x y ~ y.
Definition cif:=\b u v ~ b u v.
Definition neg:= \b~b cfa ctr.
Definition cand:= \ a b ~ \ x y~ a( b x y) y. 
Definition cor:= \ a b ~ a ctr b.

(*definition des variables*)
Definition E:=\x~x.
Definition F:=\y~y.

(*Test Conditionelle*)
Definition TestConditionnelle0:= cif ctr E F.
Compute(red_cbn TestConditionnelle0).
Definition TestConditionnelle1:= cif cfa E F.
Compute(red_cbn TestConditionnelle1).

(*Test neg, cand et cor*)
Definition TestNeg:= neg cfa. (* not false==true*)
Compute (red_cbn TestNeg).
Definition TestCand:=cand ctr cfa.
Compute (red_cbn TestCand). (* true and  false== false*)
Definition TestCor:=cor ctr cfa.
Compute (red_cbn TestCor). (* true or  false== true*)

(*definition des 1,2,3 et 4*)
Definition C0:=\f x ~ x.
Definition C1:=\f x ~ f x.
Definition C2:=\f x ~ f(f x).
Definition C3:=\f x ~ f(f(f x)).
Definition C4:=\f x ~ f(f(f(f x))).

(*definition des operateur entiers*)
Definition Csucc := \n~ \f x ~ f(n f x).
Definition   


