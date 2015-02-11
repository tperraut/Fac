Section Propositionnel.
Variables P Q R : Prop.

Theorem un : (P /\ Q) -> R -> (Q /\ R).
Proof.
 intros.
 destruct H.
 split.
 apply H1.
 apply H0.
Qed.
  
Theorem uncurry : (P -> Q -> R) -> (P /\ Q -> R).
Proof.
 intros. 
 destruct H0.
 apply H.
 assumption.
 assumption.
Qed.

Theorem contra : (P -> Q) -> ~Q -> ~P.
Proof.
 intros.
 intro.
 destruct H0.
 apply H.
 assumption.
Qed.

Theorem quatre :  (P \/ (Q /\ R)) -> P \/ Q.
Proof.
 intros.
 destruct H.
 left.
 apply H.
 right.
 destruct H.
 assumption.
Qed.

End Propositionnel.

Section Quantificateurs.
Variable p : nat -> Prop.
Theorem fimpe : (forall x:nat, p x) -> exists y:nat, p y.
Proof.
 intros.
 exists (5).
 apply H.
Qed.

Variable rel : nat -> nat -> Prop.
Theorem effe : (exists x, forall y, rel x y) -> (forall y, exists x, rel x y).
Proof.
 intros.
 destruct H as (x, H).
 exists x.
 apply H.  
Qed.

Definition le (x y:nat) : Prop := exists z:nat, y = x + z.

Theorem plus_croissante : forall x y:nat, le x (x+y).
Proof.
 intros.
 unfold le.
 exists y.
 reflexivity.
Qed.

Require Import Omega.

Theorem le_refl : forall x:nat, le x x.
Proof.
 intros.
 unfold le.
 exists 0.
 omega.
Qed.

Theorem le_trans : forall (x y z:nat), le x y /\ le y z -> le x z.
Proof.
 intros.
 unfold le.
 unfold le in H.
 destruct H.
 destruct H.
 destruct H0.
 exists (x0 + x1).
 rewrite H in H0.
 omega. 
Qed.

End Quantificateurs.

Section PurPire.
  
Variable habitant : Set.
Variable pur : habitant -> Prop.
Variable pire : habitant -> Prop.
Axiom pur_ou_pire : forall x, pur x \/ pire x.

Variable say : habitant -> Prop -> Prop.
Axiom ax_pur : forall x P, pur x -> say x P -> P.
Axiom ax_pire : forall x P, pire x -> say x P -> ~P.

Theorem au_moins_un : forall (x y:habitant), (say x (pire y)) -> (pire x \/ pire y).
Proof.
 intros.
 assert (pur x \/ pire x).
 apply pur_ou_pire.
 destruct H0.
 right.
 apply ax_pur with (x := x).
 assumption.
 assumption.
 left.
 assumption.
Qed.

Theorem deux_pour_un : forall (x y:habitant), (say x (pire x) /\ say x (pire y)) -> pire x.
Proof.
 intros.
 destruct H.
 apply au_moins_un in H.
 destruct H.
 assumption.
 assumption.
Qed.

Theorem faux_pire : forall (x:habitant), (say x False) -> (pire x).
Proof.
 intros.
 assert (pur x \/ pire x).
 apply pur_ou_pire.
 destruct H0.
 apply ax_pur with (x := x) in H.
 destruct H.
 assumption.
 assumption.
Qed.

End PurPire.

Section Relations.

  Variable A : Set.

  Definition RTot (R : A -> A -> Prop) := forall x, exists y, R x y.

  Definition RFun (R : A -> A -> Prop) := forall x y z, (R x y /\ R x z) -> y = z. 
 
  Definition Inj (R : A -> A -> Prop) := forall x y z, (R x z /\ R y z) -> x = y.

  Definition Surj (R : A -> A -> Prop) := forall y, exists x, R x y.

  Definition Inv (R : A -> A -> Prop) x y := R y x.

  Theorem inj_fun_inv : forall R, Inj R -> RFun (Inv R).
  Proof.
   intros.
   unfold RFun.
   intros.
   destruct H0.
   unfold Inv in H0.
   unfold Inv in H1.
   unfold Inj in H.
   apply H with x.
   split.
   assumption.
   assumption.
  Qed.

  Theorem fun_inj_inv : forall R, RFun R -> Inj (Inv R).
  Proof.
   intros.
   unfold Inj.
   intros.
   destruct H0.
   unfold Inv in H0.
   unfold Inv in H1.
   unfold RFun in H.
   apply H with z.
   split.
   assumption.
   assumption.
  Qed.

  Theorem tot_surj_inv : forall R, RTot R -> Surj (Inv R).
  Proof.
   intros.
   unfold Surj.
   intro.
   unfold RTot in H.
   apply H.
  Qed.

End Relations.

Section Fonctions.

  Variable A : Set.

  Definition FInj (f : A -> A) := forall x y, f x = f y -> x = y.

  Definition FSurj (f : A -> A) := forall y, exists x, f x = y.

  Definition Comp (f : A -> A) (g : A -> A) x := f (g x).

  Theorem comp_inj : forall f g, FInj f -> FInj g -> FInj (Comp f g).
  Proof.
   intros.
   unfold FInj.
   intros.
   unfold Comp in H1.
   unfold FInj in H.
   unfold FInj in H0.
   apply H in H1.
   apply H0 in H1.
   assumption.
  Qed.

  Theorem comp_surj : forall f g, FSurj f -> FSurj g -> FSurj (Comp f g).
  Proof.
(*
   intros.
   unfold FSurj in H.
   unfold FSurj in H0.
   unfold FSurj.
   unfold Comp.
   intro.
   exists y.
   apply H.
 *) 
  Qed.

End Fonctions.
