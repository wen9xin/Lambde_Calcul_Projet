(*Require Import untypedLC.*)

Section type_booleen.


Variable T : Set.
Variable N: Set. 

(* Declaration de cbool *)
Definition cbool:= T -> T -> T.

Definition ctr: cbool := fun x y => x. (* true (church) *)
Definition cfa: cbool := fun x y => y. (* false (church) *)

Definition cif: cbool->T->T->T := fun b u v => b u v. (* IF b THEN u ELSE v *)

Variable E:T.
Variable F:T.
Definition TestConditionnelle0:= cif ctr E F. (* IF ctr THEN E ELSE F *)
Compute  TestConditionnelle0. (* = E *)
Definition TestConditionnelle1:= cif cfa E F. (* IF cfa THEN E ELSE F *)
Compute  TestConditionnelle1.  (* = F *)

(* si b est cfa sortie ctr, si ctr sortie cfa *)
Definition neg: cbool->cbool := fun b => fun x y =>b y x . 
Definition testNeg:= neg ctr.  (* not true==false*)
Compute testNeg. (* => x0 *)

(* AND *)
Definition cand: cbool->cbool->cbool := fun a b => fun x y=> a( b x y) y. 
Definition testCand:= cand ctr cfa. (* true and  false== false*)
Compute testCand. (* => x0 *)

(* or *)
Definition cor:cbool->cbool->cbool:= fun a b => fun x y => a x (b x y).
Definition testCor:= cor cfa cfa. (* false or  false== false*)
Compute testCor.  (* => x0 *)

(* 1.2.2 *)

(* declaration de type cnat *)
Definition cnat:= (T->T)->(T->T).
(* codage des 5 premiers entiers de churche *)
Definition c0:cnat :=fun f x =>x .
Definition c1:cnat:=fun f x=>f x.
Definition c2:cnat:=fun f x => f(f x).
Definition c3:cnat:=fun f x => f(f(f x)).
Definition c4:cnat:=fun f x => f(f(f(f x))).

(* fonction successeur *)
Definition csucc:cnat->cnat := fun n => fun f x => f(n f x).
Definition TestCsucc:= csucc c1.
Compute  TestCsucc. (* 1++ ==2*)

(* fonction addition *)
Definition cplus:cnat->cnat->cnat := fun n m => fun f x => n f (m f x).
Definition TestCplus:= cplus c2 c3.
Compute  TestCplus. (* 2+3==5*)

(* fonction multiplication *)
Definition cmul:cnat->cnat->cnat := fun n m=> fun f => n (m f).
Definition TestCmul := cmul c2 c3.
Compute  TestCmul. (*2*3==6*)

(* fonction egale 0 *)
Definition ceq0:cnat->cbool :=fun n => fun x y => n( fun z=> y) x.
Definition TestCeq0tr := ceq0 c0.
Compute  TestCeq0tr.  (* 0==0 -> ctr*)
Definition TestCeq0fa := ceq0 c1.
Compute  TestCeq0fa. (* 1!=0 -> cfa*)