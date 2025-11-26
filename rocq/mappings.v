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
