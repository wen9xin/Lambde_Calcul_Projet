Require Import untypedLC.
(*booléens*)

(*definition des variables*)
Definition E:=\x~x. 
Definition F:=\y~y.


Definition ctr:=\x y ~ x. (* true (church) *)
Definition cfa:=\x y ~ y. (* false (church) *)


Definition cif:=\b u v ~ b u v.  (* IF b THEN u ELSE v *)
(*Test Conditionelle*)
Definition TestConditionnelle0:= cif ctr E F. (* IF ctr THEN E ELSE F *)
Compute red_cbn TestConditionnelle0. (* E= λ x · x *)
Definition TestConditionnelle1:= cif cfa E F. (* IF cfa THEN E ELSE F *)
Compute red_cbn TestConditionnelle1. (* F = λ y · y *)

(* si b est cfa sortie ctr, si ctr sortie cfa *)
Definition neg:= \b~b cfa ctr .  (* not *)
Definition TestNeg:= neg cfa. (* not false==true*)
Compute red_cbn TestNeg. (* λ x y · x *)


Definition cand:= \ a b ~ \ x y~ a( b x y) y.  (* AND *)
Definition TestCand:=cand ctr cfa. (* true and  false== false*)
Compute red_cbn TestCand.  (* λ x y · y *)


Definition cor:= \ a b ~ a ctr b. (* or *)
Definition TestCor:=cor ctr cfa. (* true or  false== true*)
Compute red_cbn TestCor.  (* λ x y · x *)


(*entiers*)
(*definition des 1,2,3 et 4*)
Definition c0:=\f x ~ x.
Definition c1:=\f x ~ f x.
Definition c2:=\f x ~ f(f x).
Definition c3:=\f x ~ f(f(f x)).
Definition c4:=\f x ~ f(f(f(f x))).

(*operateur entiers*)
Definition csucc := \n~ \f x ~ f(n f x).  (* operation successeur (n+1) *)
Definition TestCsucc:= csucc c1.
Compute red_cbn TestCsucc. (* 1++ ==2*)

Definition cplus := \n m~ \ f x ~ n f (m f x). (* operation add *)
Definition TestCplus:= cplus c2 c3.
Compute red_cbn TestCplus. (* 2+3==5*)

Definition cmul:= \n m f~ n (m f).  (* operation mult *)
Definition TestCmul := cmul c2 c3.
Compute red_cbn TestCmul. (*2*3==6*)

Definition ceq0:= \n ~\ x y~ n( \z~ y) x. (* codage de ceq0() teste à zero *)
Definition TestCeq0tr := ceq0 c0.
Compute red_cbn TestCeq0tr.  (* 0==0 -> ctr*)
Definition TestCeq0fa := ceq0 c1.
Compute red_cbn TestCeq0fa. (* 1!=0 -> cfa*)



(*Couples*)
(*Definition des fonction de couples*)
Definition cpl:= \x y ~ \k ~ k x y. (* codage d couple(x,y) *)
Definition fst:= \c~c(\u v~u). (* operation getFirst() (u,v)->u *)
Definition snd:= \c~c(\u v~v).  (* opertion getSecond() (u,v)->v *)

(*Test Couples  *)   
Definition coup:=cpl ctr cfa. (* couple(ctr,cfa) *)
Compute red_cbn (fst coup). (*λ x y · x*)
Compute red_cbn (snd coup). (*λ x y · y*)


(*Structure de choix pas fini*)

(*definition des injections*)
Definition inj1 := \x a b ~ a x.  (* a -> somme x qui a a et b *)
Definition inj2 := \x a b ~ b x.  (* b -> somme x qui a a b *)
(* Test inj1 et inj2*)
Definition TestInj1:=inj1 f g.
Compute red_cbn TestInj1. (* λ b · g f*)
Definition TestInj2:= inj2 f g.
Compute red_cbn TestInj2. (*λ b · b f*)


(*
(*donnée optionnelle*)
Definition some:= csucc .
Compute red_cbn (some c1).
Definition none:= some c0.
Compute red_cbn (none c1).
Definition coupInj:=cpl inj1 inj2.
Definition osucc1:=\x~(inj1(some x) none).


Compute red_cbn (osucc1 ).   (*λ x b a b · a (x a b) *)
Compute red_cbn (osucc1 c0). (* λ b x a · x a *)
Compute red_cbn (osucc1 c1). (* λ b x a · x (x a)*)
Compute red_cbn (osucc1 c2). (*λ b x a · x (x (x a))*)


Definition osucc2:=\x~(inj2(some x) none).
Compute red_cbn (osucc2 ).   (*λ x b · b (λ f a · f (x f a)) *)
Compute red_cbn (osucc2 c0 ). (* λ b · b (λ f x · f x) *)
Compute red_cbn (osucc2 c1). (* λ b · b (λ f x · f (f x)))*)
Compute red_cbn (osucc2 c2). (*λ b · b (λ f x · f (f (f x)))*)
*)

(*Prédécesseur*)

(* succpair prendre un couple(0,0), applique csucc pour
iterateur n fois et renvoyer un couple de (n, n+1)*)   
Definition succpair:= \p ~((\n~(cpl n (csucc n)))(snd p)).
(*on va utiliser cpred pour calculer le predecesseur *)
Definition cpredW:= \n~ fst ( n succpair (cpl c0 c0)).
Definition testcPredW:= cpredW c2. (*c2-1==c1*)
Compute red_cbn  testcPredW.

(*Factorielle*)
(* Y est le point fixe de l’op´eration f → fac’ f *)
Definition Y:= \f~(\x ~f(x x))(\x~f(x x)).
(* Fonc utilise X mult X-1 jasqu'a c1 *)
Definition Fonc := \f·\n·cif (ceq0 n) c1 (cmul n (f (cpredW n))).
(*  l’appel recursif *)
Definition Fact := Y Fonc.
Compute red_cbn (Fact c3 ).





