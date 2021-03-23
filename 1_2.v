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
Definition c0: cnat :=fun f x =>x .
Definition c1:cnat:=fun f x=>f x.