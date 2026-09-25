From Stdlib Require Export Classical_Prop.
From Stdlib Require Export ClassicalEpsilon.

(* Prop.lp *)
Definition imp (p q : Prop) : Prop := p -> q.

(* Set.lp *)
Record Type' := { type :> Type; el : type }.

(* Fol.lp *)
Definition all {a : Set} (P: a -> Prop) : Prop := forall x:a, P x.

(* Hol.lp *)
Definition arr a (b : Type') := {| type := a -> b; el := fun _ => el b |}.
Canonical arr.

(* Eq.lp *)
Lemma ind_eq : forall {a : Type'} {x y : a}, (x = y) -> forall p, (p y) -> p x.
Proof.
  intros a x y e p py. rewrite e. exact py.
Qed.
Definition neq {a : Type'} (x y : a) := ~ (x = y).

(* Bool.lp*)
Definition bool' := {| type := bool ; el := true|}.
Canonical bool'.
							 
Definition if' (b : bool) {a : Type'} (e1 : a) (e2 : a) := 
    if b then e1 else e2.

(* Comp.lp*)
Definition comparison' := {| type := comparison ; el := Eq|}.

Definition isEq (c : comparison) := 
 match c with
 | Eq => true
 | _ => false
 end.
						      
Definition isLt (c : comparison) := 
 match c with
 | Lt => true
 | _ => false
 end.	

Definition isGt (c : comparison) := 
 match c with
 | Gt => true
 | _ => false
 end.		       

Definition case_Comp := fun (A : Type') (c : comparison') (x y z : A) =>
match c with
| Eq => x
| Lt => y
| Gt => z
end.
				       
(* Epsilon.v*)
 Definition eps : forall {A : Type'}, (type A -> Prop) -> type A :=
  fun A P => epsilon (inhabits (el A)) P.
  
Lemma eps_spec {A : Type'} {P : type A -> Prop} : (exists x, P x) -> P (eps P).
Proof. intro h. unfold eps. apply epsilon_spec. exact h. Qed.


