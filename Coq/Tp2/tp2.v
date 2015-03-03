Require Import Classical.

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

 (*Theorem comp_surj : forall f g, FSurj f -> FSurj g -> FSurj (Comp f g).
  Proof.
   intros.
   unfold FSurj in H.
   unfold FSurj in H0.
   unfold FSurj.
   unfold Comp.
   intro.
   exists y.
   apply H. 
  Qed.
*)

End Fonctions.

Section Ensembles_finis.

  Definition FFInj (n:nat) (f:nat->nat) :=
    forall x y, x<n -> y<n -> f(x)=f(y) -> x=y.

  Definition FFMono (n:nat) (f:nat->nat) :=
    forall x y, x<y -> y<n -> f(x)<f(y).

  Require Import Omega.

  Theorem mono_inj : forall f n, FFMono n f -> FFInj n f.
  Proof.
    intros.
    unfold FFInj.
    unfold FFMono in H.
    intros.
    assert (x = y \/ x < y \/ x > y).
    omega.
    destruct H3.
    assumption.
    destruct H3.
    apply H in H3.
    omega.
    assumption.
    apply H in H3.
    omega.
    assumption.
  Qed.

 Theorem mono_domain :
     forall n f, FFMono (S n) f -> exists x, x<=n /\ f(x) >= n.
  Proof.
    intros.
    induction n.
    exists 0.
    omega.
    assert (FFMono (S n) f).
    admit.
    apply IHn in H0.
    destruct H0.
    assert ((x <= n /\ n < f x) \/ (x <= n /\ n = f x)).
    omega.
    destruct H1.
    exists n.
    split.
    omega.  
  Qed.

End Ensembles_finis.

Section Parite.

 Inductive pair : nat -> Prop :=
  | pair_0 : pair 0
  | pair_ss : forall x, pair x -> pair (S (S x)).

 Check pair_ind.

 Inductive impair : nat -> Prop :=
  | impair_1 : impair 1
  | impair_s2 : forall x, impair x -> impair (S (S x)).

 Lemma spi : forall x, pair x -> impair (S x).
 Proof.
  intros.
  induction H.
  apply impair_1.
  apply impair_s2.
  assumption.
 Qed.

 Lemma sip : forall x, impair x -> pair (S x).
 Proof.
  intros.
  induction H.
  apply pair_ss.
  apply pair_0.
  apply pair_ss.
  assumption.
 Qed.

 Lemma poi : forall x, pair x \/ impair x.
 Proof.
  intros.
  induction x.
  left.
  apply pair_0.
  destruct IHx.
  apply spi in H.
  right.
  assumption.
  apply sip in H.
  left.
  assumption.
 Qed.

End Parite.
