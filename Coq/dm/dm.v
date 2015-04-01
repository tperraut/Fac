(* Devoir Maison *)

(* Perraut Thomas *)

Section LogiquePropositionnelle.

 Variables P Q R : Prop.

 Lemma q1a : (P -> Q) /\ (Q -> R) -> P -> R.
 Proof.
  intros.
  destruct H.
  apply H1.
  apply H.
  assumption.
 Qed.

 Lemma q1b : ((P /\ Q) -> R) -> (P -> Q -> R).
 Proof.
  intros.
  apply H.
  split.
  apply H0.
  apply H1.
 Qed.
(*
** Lemma q1c : (P -> Q -> R) -> (P -> R).
** Cet enonce est faux, contre-exemple :
** - P  Vrai, Q Faux et R Faux donne 
**   (Vrai -> Faux -> Vrai) -> (Vrai -> Faux)
**<->(Faux -> Vrai) -> Faux
**<->Vrai -> Faux  
*)

(*
** Lemma q1d : (P \/ Q)`-> (P /\ Q).
** Cet enonce est faux, contre-exemple :
**  - P vrai et Q faux donne vrai -> faux
*)

 Lemma q1e : (P /\ Q) -> (P \/ Q).
 Proof.
  intro.
  destruct H.
  left.
  assumption.
 Qed.

 Lemma q1f : (P \/ Q) -> (Q \/ P).
 Proof.
  intro.
  destruct H.
  right.
  assumption.
  left.
  assumption.
 Qed.

 Lemma q1g : (P \/ Q) -> (~P) -> Q.
 Proof.
  intros.
  destruct H as [H1|H2].
  destruct H0.
  assumption.
  assumption.
 Qed.

(*
** Lemma q1h : (P -> Q) -> ~(Q -> P).
** Cet enonce est faux, contre-exemple :
**  - P vrai et Q vrai donne vrai -> faux
*)

End LogiquePropositionnelle.

Section Quantificateurs.

 Variable A : Set.
 Variable R : A -> A -> Prop.

 Definition f1 := forall x, exists y, R x y /\ R y x.
 
 Definition f2 := forall x, exists y, R x y \/ R y x.

 Definition f3 := forall x y z, (R x y /\ R y z) -> R x z.

 Definition f4 := exists x, R x x.

 Lemma q2 : f1 -> f2.
 Proof.
  intro.
  unfold f1 in H.
  unfold f2.
  intros.
  destruct (H x).
  exists x0.
  apply q1e.
  assumption.
 Qed.

 Lemma q3 : f1 -> (f3 -> f4).
 Proof.
  intros.
  unfold f1 in H.
  unfold f3 in H0.
  unfold f4.
  
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

End RecurrenceForte.