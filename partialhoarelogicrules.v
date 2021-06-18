From HoareTut Require Import hoarelogicsemantics.
From HoareTut Require Import partialhoarelogic.

Module PartialHoareLogicRules (HD: HoareLogicDefs).

  Export HD.

  Module PHL := PartialHoareLogic(HD).
  Export PHL.


  Lemma synt_wp_skip: forall {pre: Pred}, pre |= synt_wp Iskip pre.
  Proof.
    auto.
  Qed.

  Lemma wp_skip: forall {pre: Pred}, pre |= Iskip {= pre =}.
  Proof.
    intro pre. apply soundness, synt_wp_skip.
  Qed.


  Lemma synt_wp_set:
    forall {A: Type} {x: E.Var A} {expr: E.Expr A} {pre: Pred},
      (fun e => pre (E.upd x (E.eval expr e) e)) |= synt_wp (Iset x expr) pre.
  Proof.
    auto.
  Qed.

  Lemma wp_set:
    forall {A: Type} {x: E.Var A} {expr: E.Expr A} {pre: Pred},
      (fun e => pre (E.upd x (E.eval expr e) e)) |= Iset x expr {= pre =}.
  Proof.
    intros A x expr pre. apply soundness, synt_wp_set.
  Qed.


  Lemma synt_wp_if:
    forall {cond: E.Expr bool} {p q: ImpProg} {pre post: Pred},
      (fun e => E.eval cond e = true /\ pre e) |= synt_wp p post ->
      (fun e => E.eval cond e = false /\ pre e) |= synt_wp q post ->
      pre |= synt_wp (Iif cond p q) post.
  Proof.
    intros cond p q pre post H1 H2 e. unfold synt_wp. fold synt_wp.
    specialize (H1 e). specialize (H2 e). split; auto.
  Qed.

  Lemma wp_if:
    forall {cond: E.Expr bool} {p q: ImpProg} {pre post: Pred},
      (fun e => E.eval cond e = true /\ pre e) |= p {= post =} ->
      (fun e => E.eval cond e = false /\ pre e) |= q {= post =} ->
      pre |= Iif cond p q {= post =}.
  Proof.
    intros cond p q pre post H1 H2.
    apply soundness, synt_wp_if; now apply completeness.
  Qed.


  Lemma synt_wp_seq:
    forall {p q: ImpProg} {pre post: Pred} (mid: Pred),
      pre |= synt_wp p mid -> mid |= synt_wp q post ->
      pre |= synt_wp (Iseq p q) post.
  Proof.
    intros p q pre post mid H1 H2. unfold synt_wp. fold synt_wp.
    remember (synt_wp q post) as mid'.
    assert (synt_wp p mid |= synt_wp p mid') as H.
    - now eapply synt_wp_monotonic.
    - intros e Hpre. specialize (H1 e Hpre). exact (H e H1).
  Qed.

  Lemma wp_seq:
    forall {p q: ImpProg} {pre post: Pred} (mid: Pred),
      pre |= p {= mid =} -> mid |= q {= post =} -> pre |= Iseq p q {= post =}.
  Proof.
    intros p q pre post mid H1 H2.
    apply soundness, (synt_wp_seq mid); now apply completeness.
  Qed.


  Lemma synt_wp_while:
    forall {cond: E.Expr bool} {p: ImpProg} {inv: Pred},
      (fun e => inv e /\ E.eval cond e = true) |= synt_wp p inv ->
      inv |= synt_wp (Iwhile cond p) (fun e => E.eval cond e = false /\ inv e).
  Proof.
    intros cond p inv H e Hinv. unfold synt_wp. fold synt_wp.
    exists inv. repeat split; auto.
  Qed.

  Lemma wp_while:
    forall {cond: E.Expr bool} {p: ImpProg} {inv: Pred},
      (fun e => inv e /\ E.eval cond e = true) |= p {= inv =} ->
      inv |= Iwhile cond p {= fun e => E.eval cond e = false /\ inv e =}.
  Proof.
    intros cond p inv H. now apply soundness, synt_wp_while, completeness.
  Qed.


Lemma synt_unwind_while:
  forall {p: E.Expr bool} {c: ImpProg} {pre post: Pred},
    pre |= synt_wp (Iwhile p c) post ->
    pre |= synt_wp (Iif p (Iseq c (Iwhile p c)) Iskip) post.
Proof.
  intros p c pre post. unfold synt_wp. fold synt_wp.
  intros Hinv e Hpre. specialize (Hinv e Hpre). destruct Hinv as [inv Hinv].
  destruct Hinv as [Hinv Hpost]. split.
  - intro Hcond. eapply synt_wp_monotonic with (post1:=inv).
    + intros e' Hinv'. exists inv. now split.
    + destruct Hpost as [_ Htrue]. exact (Htrue e Hinv Hcond).
  - destruct Hpost as [Hfalse _]. exact (Hfalse e Hinv).
Qed.

Lemma unwind_while:
  forall {p: E.Expr bool} {c: ImpProg} {pre post: Pred},
    pre |= Iwhile p c {= post =} ->
    pre |= Iif p (Iseq c (Iwhile p c)) Iskip {= post =}.
Proof.
  intros p c pre post H. now eapply soundness, synt_unwind_while, completeness.
Qed.

End PartialHoareLogicRules.
