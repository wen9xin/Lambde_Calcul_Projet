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
(* n avec une fois de ++ *)
Definition csucc := \n~ \f x ~ f(n f x).  (* operation successeur (n+1) *)
Definition TestCsucc:= csucc c1.
Compute red_cbn TestCsucc. (* 1++ ==2*)

(* m avec n fois de ++ *)
Definition cplus := \n m~ \ f x ~  n f (m f x). (* operation add *)
Definition TestCplus:= cplus c2 c3.
Compute show_cbn TestCplus. (* 2+3==5*)

(*m avec n fois de +m *)
Definition cmul:= \n m f~ n (m f).  (* operation mult *)
Definition TestCmul := cmul c2 c3.
Compute red_cbn TestCmul. (*2*3==6*)

(* utilise n pour choisir x ou y sur (\z~y)x *)
Definition ceq0:= \n ~\ x y~ n( \z~ y) x. (* codage de ceq0() teste à zero *)
Definition TestCeq0tr := ceq0 c0.
Compute show_cbn TestCeq0tr.  (* 0==0 -> ctr*)
Definition TestCeq0fa := ceq0 c1.
Compute show_cbn TestCeq0fa. (* 1!=0 -> cfa*)




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
Definition inj2 := \x a b ~ b x.  (* b -> somme x qui a a et b *)
(* Test inj1 et inj2*)
Definition TestInj1:=inj1 f g.
Compute red_cbn TestInj1. (* λ b · g f*)
Definition TestInj2:= inj2 f g.
Compute red_cbn TestInj2. (*λ b · b f*)



(*Prédécesseur*)


(* codage d'operation Iteration, i'operation applique une fonction g
   n fois sur un nombre x*)   
Definition iter:= \n g x ~ n g x.
(* succCouple prendre an couple et renvoyer un couple de (x, y+1)
   on va utiliser succCouple pour calculer le predecesseur *)
Definition succCouple:=\c~ cpl (snd c) (csucc (snd c )).
(* cpred calcule le predecesseur d'un nombre n, pour calculer le pred
   on itére n-1 fois de zero calculant le successeur. on va utiliser
   le fonction iter pour appliquer la fonction succCouple sur une cople (0, 0) n fois
   comme ca le resulta sera le fst du couple renvoyée *)
Definition cpred:=\n~ fst(iter n succCouple(cpl c0 c0)).

(* 
(* succpair prendre un couple(0,0), applique csucc pour
iterateur n fois et renvoyer un couple de (n, n+1)*)
Definition succCouple:= \p ~((\n~(cpl n (csucc n)))(snd p)).
(*on va utiliser cpred pour calculer le predecesseur *)
Definition cpred:= \n~ fst ( n succCouple (cpl c0 c0)). *)

Definition testcPred:= cpred c2. (*c2-1==c1*)
Compute red_cbn  testcPred.

(*Factorielle*)
(* Y est le point fixe de l’op´eration f → fac’ f *)
Definition Y:= \f~(\x ~f(x x))(\x~f(x x)).
(* Fonc utilise X mult X-1 jasqu'a c1 *)
Definition Fonc := \f·\n·cif (ceq0 n) c1 (cmul n (f (cpred n))).
(*  l’appel recursif *)
Definition Fact := Y Fonc.
Compute red_cbn (Fact c3 ).





