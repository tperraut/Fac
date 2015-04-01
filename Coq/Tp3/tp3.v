
(* EXO mots *)
Section MOTS.

Variable char : Set.
Variable a : char.
Variable b : char.

Require Import List.
Definition word : Set := list char.

Definition pempty (w:word) : Prop := (w = nil).
Definition pchar (c:char) (w:word) : Prop := (w = c::nil).

Definition pconcat (p1:word -> Prop) (p2:word -> Prop) (w : word):= 
  exists x : word, exists y : word, w = x++y /\ (p1 x /\ p2 y).

Theorem pconcat_empty : forall p w, pconcat p pempty w -> p w.
Proof.
 intros.
 unfold pconcat in H.
 destruct H.
 destruct H.
 destruct H.
 destruct H0.
 unfold pempty in H1.
 rewrite H1 in H.
 rewrite <- app_nil_end in H.
 rewrite H.
 assumption.
Qed.

Inductive pstar (p:word -> Prop) : word -> Prop := 
 | pstar_0 : pstar p nil
 | pstar_1 : forall x : word, p x -> pstar p x
 | pstar_n : forall x : word, forall y : word, pstar p x -> pstar p y -> pstar p (x++y)
.

Theorem star_concat :
  forall (p:word->Prop) w1 w2,  p w1 -> pstar p w2 -> pstar p (app w1 w2).
Proof.
intros.
induction w1.
simpl.
assumption.
apply pstar_n.
apply pstar_1.
assumption.
assumption.
Qed.

Theorem concat_star :
  forall (p:word->Prop) w1 w2,  pstar p w1 -> p w2 -> pstar p (app w1 w2).
Proof.
intros.
apply pstar_n.
assumption.
apply pstar_1.
assumption.
Qed.

Theorem star_pconcat : 
  forall (p:word->Prop) w, pconcat (pstar p) p w -> pstar p w.
Proof.
intros.
unfold pconcat in H.
destruct H.
destruct H.
destruct H.
destruct H0.
rewrite H.
apply pstar_n.
assumption.
apply pstar_1.
assumption.
Qed.

End MOTS.
