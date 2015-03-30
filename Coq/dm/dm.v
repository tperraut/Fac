(* Devoir Maison *)

(* Rappelez votre nom ici ! *)

Section LogiquePropositionnelle.

(* Faites vos preuves de l'exercice 1 ici. *)

End LogiquePropositionnelle.




Section Quantificateurs.

Definition f1 := (* À compléter *) .
 
Definition f2 := (* À compléter *) .

Definition f3 := (* À compléter *) .

Definition f4 := (* À compléter *) .

Lemma q2 : f1 -> f2.
Proof.
(* À compléter *)
Qed.

Lemma q3 : f1 -> (f3 -> f4).
Proof.
(* À compléter *)
Qed.

End Quantificateurs.




Section RelationsInductives.

Parameter X : Type.
Parameter ami : X -> X -> Prop.
Axiom ami_sym : forall x y, ami x y -> ami y x.

Inductive lien : X -> X -> Prop :=
(* À compléter *)
.

Lemma ami_droite :
forall x y z, lien x z -> ami z y -> lien x y.
Proof.
(* À compléter *)
.

Theorem lien_sym :
forall x y, lien x y -> lien y x.
Proof.
(* À compléter *)
.

End RelationsInductives.




Section RecurrenceForte.

Require Import Omega.

Definition upto (P: nat -> Prop) (n: nat) : Prop := forall m, m<n -> P m.

Lemma upto_forall :
forall P : nat -> Prop,
(forall a, upto P a) -> (forall n, P n).
Proof.
(* À compléter *)
Qed.

Lemma rec_upto :
forall P : nat -> Prop,
(forall n, upto P n -> P n) ->
forall a, upto P a.
Proof.
(* À compléter *)
Qed.

Lemma rec_forte :
forall P : nat -> Prop,
(forall n : nat, upto P n -> P n) ->
forall n : nat, P n.
Proof.
(* À compléter *)
Qed.

Definition divise (a n : nat) : Prop :=
exists q, a * q = n.

Definition premier (n : nat) : Prop :=
forall a, divise a n -> a = 1 \/ a = n.

Axiom premier_ou_divisible :
forall n, n>1 -> premier n \/ exists d, divise d n /\ d > 1 /\ d < n.

Axiom division_transitive :
forall a b c, divise a b -> divise b c -> divise a c.

Lemma diviseur_premier :
forall n, n>1 -> exists d, divise d n /\ premier d.
Proof.
(* À compléter *)
Qed.
