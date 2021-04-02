(* Type de l’identite polymorphe *)
Definition tid : Set := forall T: Set, T -> T.  (* \/T,T->T *)
Definition id : tid := fun T:Set => fun x:T => x.  (* /\T.\x^T *)

(* 2.1.1 *)
Compute id nat 3. (* =3:nat  test l’identité polymorphe sur nat et bool *)

(* 2.1.2 *)
Definition nbtrue1 := 
fun b =>match b with true => 1 | false => 0 end. (* bool-> nat *)
 (* fun b : bool => if b then 1 else 0 *)

(* 2.1.3 *)
Compute id tid id. (* = fun (T : Set) (x : T) => x     : tid *)



(* 2.2.1 *)
Definition pbool : Set := forall T: Set, T -> T -> T.
Definition ptr: pbool := fun T:Set => fun x y:T => x. (* /\T.\x^T y^T.x *)
Definition pfa: pbool := fun T:Set => fun x y:T => y. (* /\T.\x^T y^T.y *)

(* 2.2.2 *)
Definition pneg: pbool->pbool := 
fun b => fun T:Set => fun x y:T=> b T y x.
(* \b./\T.\x^T y^T. b T y x *)
Definition testNeg1:= pneg ptr. (* not ptr==pfa *)
Compute testNeg1. (* fun (T : Set) (_ x0 : T) => x0 :pbool *)
Definition testNeg2:= pneg pfa. (* not pfa==ptr *)
Compute testNeg2. (* = fun (T : Set) (x _ : T) => x :pbool*)

(* 2.2.3 *)
(* conjonction *)
Definition pand: pbool->pbool->pbool :=
 fun a b => fun T:Set => fun x y:T=> a T ( b T x y) y. 
(* \a b./\T.\x^T y^T.a T ( b T x y) y *)
Definition testPand1:= pand ptr pfa. (* true and false==false *)
Compute testPand1. (* x0 *)
Definition testPand2:= pand ptr ptr. (* true and true==true *)
Compute testPand2. (* x *)
(* disjonction *)
Definition por:pbool->pbool->pbool:= 
fun a b => fun T:Set => fun x y:T => a T x (b T x y).
(* \a b./\T.\x^T y^T.a T x( b T x y) *)
Definition testPor1:= por pfa pfa. (* false or false==false *)
Compute testPor1. (* x0 *)
Definition testPor2:= por ptr pfa. (* true or false==true *)
Compute testPor2. (* x *)

(* 2.2.4 *)
Definition pif: pbool->nat->nat->nat := 
fun b =>fun u v:nat => b nat u v.
(* if pbool then u else v*)
Definition v3f5:pbool->nat:=fun k=> pif k  3 5.
(* u=3, v=5 *)
Compute v3f5 ptr. (* ptr -> 3 *)
Compute v3f5 pfa. (* pfa -> 5 *)

(* 2.2.5 *)
Definition tpbool: Set :=
 forall pbool:Set, pbool->pbool.  (* \/pbool,pbool->pbool *)
Definition iPbool : tpbool := fun pbool:Set => fun b:pbool => b. (* /\pbool.\x^pbool *)
Compute iPbool tpbool iPbool.      
(* = fun (pbool : Set) (x : pbool) => x
     : tpbool *)

(* 2.3.1.1 *)
Definition pprod_nb : Set :=
 forall T:Set, (nat->bool->T)->T.
Definition pcpl_nb : nat-> bool-> pprod_nb := 
fun a b (T:Set) (K : nat->bool->T) => K a b.
Compute pcpl_nb 2 true.

(* 2.3.1.2  *)
Definition pprod_bn : Set :=
 forall T:Set, (bool->nat->T)->T.
Definition pcpl_bn : bool -> nat -> pprod_bn := 
fun a b (T:Set) (K : bool->nat->T) => K a b.
Compute pcpl_bn false 3.

(* 2.3.1.3 *)
Definition fst : pprod_nb->nat :=
fun c => c nat (fun u v => u).
Definition snd : pprod_nb->bool :=
fun c => c bool (fun u v => v).
Compute fst (pcpl_nb 4 true).
Compute snd (pcpl_nb 5 false).
Definition nbAbn : pprod_nb->pprod_bn :=
fun c => pcpl_bn (snd c) (fst c).
Compute nbAbn (pcpl_nb 4 true).


(* 2.3.1.4 *)
Definition pprod : Set -> Set -> Set := 
fun A B => forall T:Set,(A -> B -> T) -> T.
(* A et B sont Set, et on cree A * B qui est en type T, donc on a (A->B->T)  *)
Definition pcpl(A B: Set): A->B->pprod A B := 
fun a b => fun T:Set => fun K:A->B->T => K a b.
(* On prend le A*B (pprod) a -> pcpl A B, en type -> T, donc on a (A->B->T)->T
Et dans /\ T. \k ^ A->B->T .k a b, T est Set; k est pprod *)
Variable E:Set.
Variable F:Set.
Compute pcpl E F.

(* 2.3.2 *)
Definition psom (A B: Set) : Set := 
forall T:Set, (A -> T) -> (B -> T) -> T.
Definition inj1 (A B: Set) : A -> psom A B :=
 fun a => fun T:Set => fun K:A->T =>fun Q:B->T => K a .
Definition inj2 (A B: Set) : B -> psom A B := 
fun b => fun T:Set => fun K:A->T =>fun Q:B->T => Q b .
(* Definition toutvr: psom pbool (pprod pbool pbool) -> pbool:=  *)



(* 2.4.1 *)
Definition pnat : Set := forall T: Set, (T -> T)->(T->T).  (* \/T,(T -> T)->(T->T) *)
Definition p0:pnat:= fun T:Set=> fun f:T->T=>fun x:T =>x. (* /\T.\f^T->T x^T.x *)
Definition p1:pnat:= fun T:Set=> fun f:T->T=>fun x:T =>f x .
Definition p2:pnat:= fun T:Set=> fun f:T->T=>fun x:T => f(f x) .
Definition p3:pnat:= fun T:Set=> fun f:T->T=>fun x:T =>f(f(f x)) .
Definition p4:pnat:= fun T:Set=> fun f:T->T=>fun x:T =>f(f(f(f x))).
Definition p5:pnat:= fun T:Set=> fun f:T->T=>fun x:T =>f(f(f(f(f x)))).
Definition pS:pnat->pnat:= fun n:pnat => fun T:Set=> fun f x => f(n T f x).
(* \ n ^ pnat . /\T.\f x->f ( n T f x) *)

Definition pplus: pnat->pnat->pnat:= 
fun n m =>fun T:Set=> fun f x => n T f ( m T f x). 
Definition TestPplusl:= pplus p2 p3.
Compute  TestPplusl. (* 2+3==5*)

Definition pmul :pnat->pnat->pnat := 
fun n m=>fun T:Set=> fun f => n T (m T f).
Definition TestPmul := pmul p2 p3.
Compute  TestPmul. (*2*3==6*)

Definition peq0:pnat->pbool :=
fun n =>fun T:Set=> fun x y => n T( fun z=> y) x.
Definition TestPeq0tr := peq0 p0.
Compute  TestPeq0tr.  (* 0==0 -> ptr*)
Definition TestPeq0fa := peq0 p1.
Compute  TestPeq0fa. (* 1!=0 -> pfa*)

(* 2.4.2 *)
Definition pplus2:pnat->pnat->pnat := 
fun n m:pnat=> n pnat pS m.
Definition Testplus2:= pplus2 p2 p3.
Compute  Testplus2. (* 2+3==5*)

(* 2.4.3 *)


