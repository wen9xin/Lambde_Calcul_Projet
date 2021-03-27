(*Require Import untypedLC.*)

Section type_booleen.


Variable T : Set.
Variable N: Set. 

Definition cbool:= T -> T -> T.
Definition ctr: cbool := fun x y => x.
Definition cfa: cbool := fun x y => y.
Definition cif: cbool->T->T->T := fun b u v => b u v.

Variable E:T.
Variable F:T.
Definition TestConditionnelle0:= cif ctr E F.
Compute  TestConditionnelle0.
Definition TestConditionnelle1:= cif cfa E F.
Compute  TestConditionnelle1.

Definition neg: cbool->cbool := fun b => fun x y =>b y x . 
Definition testNeg:= neg ctr.
Compute testNeg.

Definition cand: cbool->cbool->cbool := fun a b => fun x y=> a( b x y) y. 
Definition testCand:= cand ctr cfa.
Compute testCand.

Definition cor:cbool->cbool->cbool:= fun a b => fun x y => a x (b x y).
Definition testCor:= cor cfa cfa.
Compute testCor.


Definition cnat:= (T->T)->(T->T).
Definition c0:cnat :=fun f x =>x .
Definition c1:cnat:=fun f x=>f x.
Definition c2:cnat:=fun f x => f(f x).
Definition c3:cnat:=fun f x => f(f(f x)).
Definition c4:cnat:=fun f x => f(f(f(f x))).

Definition csucc:cnat->cnat := fun n => fun f x => f(n f x).
Definition TestCsucc:= csucc c1.
Compute  TestCsucc. (* 1++ ==2*)

Definition cplus:cnat->cnat->cnat := fun n m => fun f x => n f (m f x).
Definition TestCplus:= cplus c2 c3.
Compute  TestCplus. (* 2+3==5*)

Definition cmul:cnat->cnat->cnat := fun n m=> fun f => n (m f).
Definition TestCmul := cmul c2 c3.
Compute  TestCmul. (*2*3==6*)

Definition ceq0:cnat->cbool :=fun n => fun x y => n( fun z=> y) x.
Definition TestCeq0tr := ceq0 c0.
Compute  TestCeq0tr.  (* 0==0 -> ctr*)
Definition TestCeq0fa := ceq0 c1.
Compute  TestCeq0fa. (* 1!=0 -> cfa*)