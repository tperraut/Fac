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
 Variable cst : A.
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
  exists cst.
  destruct (H cst).
  destruct H1.
  apply H0 with (y:=x).
  split.
  assumption.
  assumption.
 Qed.

 End Quantificateurs.




 Section RelationsInductives.

 Parameter X : Type.
 Parameter ami : X -> X -> Prop.
 Axiom ami_sym : forall x y, ami x y -> ami y x.

 Inductive lien : X -> X -> Prop :=
  | lien_xy : forall x : X, forall y : X, ami x y -> lien x y
  | lien_xzy : forall x y z, ami x z -> lien z y -> lien x y
 .

 Lemma ami_droite :
 forall x y z, lien x z -> ami z y -> lien x y.
 Proof.
  intros.
  induction H.
  apply lien_xzy with y0.
  assumption.
  apply lien_xy.
  assumption.
  apply lien_xzy with z.
  assumption.
  apply IHlien.
  assumption.
 Qed.

 Theorem lien_sym :
 forall x y, lien x y -> lien y x.
 Proof.
  intros.
  induction H.
  apply lien_xy.
  apply ami_sym.
  assumption.
  apply ami_droite with z.
  assumption.
  apply ami_sym.
  assumption.
 Qed.

End RelationsInductives.


Section RecurrenceForte.

 Require Import Omega.

 Definition upto (P: nat -> Prop) (n: nat) : Prop := forall m, m < n -> P m.

 Lemma upto_forall :
 forall P : nat -> Prop,
 (forall a, upto P a) -> (forall n, P n).
 Proof.
  intros.
  apply H with (S n).
  omega.
 Qed.

 Lemma rec_upto :
 forall P : nat -> Prop,
 (forall n, upto P n -> P n) ->
 forall a, upto P a.
 Proof.
  intros.
  induction a.
  unfold upto.
  intros.
  omega.
  unfold upto.
  intros.
  unfold upto in IHa.
  apply H.
  unfold upto.
  intros.
  apply IHa.
  omega.
 Qed.

 Lemma rec_forte :
 forall P : nat -> Prop,
 (forall n : nat, upto P n -> P n) ->
 forall n : nat, P n.
 Proof.
  intro.
  intro.
  induction n.
  apply H.
  unfold upto.
  intros.
  omega.
  apply H.
  unfold upto.
  intros.
  apply H.
  unfold upto.
  intros.
  apply rec_upto with n.
  intros.
  apply H.
  assumption.
  omega.
 Qed.

 Definition divise (a n : nat) : Prop :=
 exists q, a * q = n.

 Definition premier (n : nat) : Prop :=
 forall a, divise a n -> a = 1 \/ a = n.

 Axiom premier_ou_divisible :
 forall n, n > 1 -> premier n \/ exists d, divise d n /\ d > 1 /\ d < n.

 Axiom division_transitive :
 forall a b c, divise a b -> divise b c -> divise a c.

 Lemma diviseur_premier :
 forall n, n > 1 -> exists d, divise d n /\ premier d.
 Proof.
  intros.
  apply rec_forte with (n := n).
  unfold upto.
  intros.
  unfold upto in H0.
  apply H0.
 Qed.

End RecurrenceForte.