Require Import untypedLC.


(*booléens*)
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
Compute red_cbn TestConditionnelle0.
Definition TestConditionnelle1:= cif cfa E F.
Compute red_cbn TestConditionnelle1.
(*Test neg, cand et cor*)
Definition TestNeg:= neg cfa. (* not false==true*)
Compute red_cbn TestNeg.
Definition TestCand:=cand ctr cfa.
Compute red_cbn TestCand. (* true and  false== false*)
Definition TestCor:=cor ctr cfa.
Compute red_cbn TestCor. (* true or  false== true*)


(*entiers*)
(*definition des 1,2,3 et 4*)
Definition c0:=\f x ~ x.
Definition c1:=\f x ~ f x.
Definition c2:=\f x ~ f(f x).
Definition c3:=\f x ~ f(f(f x)).
Definition c4:=\f x ~ f(f(f(f x))).
(*definition des operateur entiers*)
Definition csucc := \n~ \f x ~ f(n f x).
Definition cplus := \n m~ \ f x ~ n f (m f x).
Definition cmul:= \n m ~ n (m f).
Definition ceq0:= \n ~\ x y~ n( \z~ y) x.
(*Test entiers*)
Definition TestCsucc:= csucc c1.
Compute red_cbn TestCsucc. (* 1++ ==2*)
Definition TestCplus:= cplus c2 c3.
Compute red_cbn TestCplus. (* 2+3==5*)
Definition TestCmul := cmul c2 c3.
Compute red_cbn TestCmul. (*2*3==6*)
Definition TestCeq0tr := ceq0 c0.
Compute red_cbn TestCeq0tr.  (* 0==0 -> ctr*)
Definition TestCeq0fa := ceq0 c1.
Compute red_cbn TestCeq0fa. (* 1!=0 -> cfa*)


(*Couples*)
(*Definition des fonction de couples*)
Definition cpl:= \x y ~ \k ~ k x y.
Definition fst:= \c~c(\u v~u).
Definition snd:= \c~c(\u v~v).
(*Test Couples (\k~k ctr cfa) *)   
Definition coup1:= \k~k ctr cfa.
Compute red_cbn (fst coup1).
Compute red_cbn (snd coup1).
(*Test Couples (cpl ctr cfa) *)
Definition coup2:=cpl ctr cfa.
Compute red_cbn (fst coup2).
Compute red_cbn (snd coup2).


(*Structure de choix pas fini*)
(*definition des injections*)
Definition inj1 := \x~\a b ~ a x.
Definition inj2 := \x~\a b ~ b x.
(* Test inj1 et inj2*)
Definition TestInj1:=inj1 f g.
Compute red_cbn TestInj1. (* retour gf*)
Definition TestInj2:= inj2 f g.
Compute red_cbn TestInj2. (* retour bf*)
(*
Definition double:= cmul c2 c3.
Definition negative:= neg ctr.
Definition doubleTest:= inj1 double negative.
Compute red_cbn doubleTest.
Definition negativeTest:= inj2 double negative.
Compute red_cbn negativeTest. 

(*donnée optionnelle*)

Definition some:= inj1 f.
Compute red_cbn some.
Definition none:=c0.
Definition osucc:=some none.
Compute red_cbn osucc.
Definition osucc2:=inj2 some none.
Compute red_cbn osucc2.
*)

(*Prédécesseur*)
(* Definition*)
Definition succ1:= (csucc n).
Definition succpair:= \p ~((\n~(cpl n (csucc n)))(snd p)).
Definition cpred:= \n~ fst ( n succpair (cpl c0 c0)).
Definition testcPred:= cpred c2. (*c2-1==c1*)
Compute red_cbn  testcPred.

(*Factorielle*)
Definition succf:=\p~p(\x n~( cpl (f x n) (csucc n))).



