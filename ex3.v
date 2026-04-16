From Project Require Import ex1.
From Project Require Import ex2.
From Stdlib Require Import List.
Import ListNotations.

Inductive ae : list form -> form -> Prop :=
  | AEAsm A s: In s A -> ae A s 
  | AEElim A s t: ae A (s ~> t) -> cf A s -> ae A t

with cf : list form -> form -> Prop :=
  | CFIntro A s t : cf (s::A) t -> cf A (s~>t)
  | CFIncl A s : ae A s -> cf A s
.

Notation "A |-cf s":= (cf A s) (at level 70).
Notation "A |-ae s":= (ae A s) (at level 70).

Scheme cf_ind_mut := Induction for cf Sort Prop
with ae_ind_mut := Induction for ae Sort Prop.
Combined Scheme cf_ae_ind from cf_ind_mut, ae_ind_mut.
Check cf_ae_ind.

(* Lemma 1*)

(* I had a lot of difficulties to use the induction Scheme so I
   applied the induction "lemma" directly *)
Lemma Weakcfae:
  ((forall A s (c:cf A s), (forall B, incl A B -> cf B s)) /\
  (forall A s (a:ae A s), (forall B, incl A B -> ae B s))).
Proof.
  apply cf_ae_ind.
  - intros.
    apply CFIntro.
    apply H.
    apply add_head_incl.
    apply H0.
  - intros.
    apply CFIncl.
    apply H.
    apply H0.
  - intros. 
    apply AEAsm.
    apply H.
    apply i.
  - intros. 
    eapply AEElim.
    + apply H.
      apply H1.
    + apply H0.
      apply H1.
Qed.

(* I separated the previous result into two pleasant lemma 
   in case I need to use it *)

Lemma Weakcf A B s:
  cf A s -> incl A B -> cf B s.
Proof.
  destruct Weakcfae as [h _].
  intros.
  eapply h.
  - apply H.
  - apply H0.
Qed.

Lemma Weakae A B s:
  ae A s -> incl A B -> ae B s.
Proof.
  destruct Weakcfae as [ _ h].
  intros.
  eapply h.
  - apply H.
  - apply H0.
Qed.

(* Model *)

Definition cut_free_syntactic_model : WModel.
Proof.
  refine {|
    world := list form;
    rel := @incl (form);
    mbot := fun A => cf A bot;
    inter := fun A n => cf A (var n)
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros w w' [inc bo].
    eapply Weakcf.
    + apply bo.
    + apply inc.
  - intros w w' n [inc ded].
    eapply Weakcf.
    all: eassumption.
Defined.

(* Lemma 2 *)

Lemma Correctness A s:
  (winterp cut_free_syntactic_model A s -> cf A s )/\
  (ae A s -> winterp cut_free_syntactic_model A s).
Proof.
  induction s in A |-*.
  - split.
    + simpl. 
      easy.
    + simpl.
      apply CFIncl.
  - split.
    + simpl.
      easy.
    + simpl.
      apply CFIncl.
  - split.
    + simpl.
      intro h.
      apply CFIntro.
      apply IHs2.
      apply h.
      split.
      * apply incl_cons'.
      * apply IHs1.
        apply AEAsm.
        now left.
    + simpl.
      intros ded A' [inc int].
      apply IHs2.
      eapply AEElim.
      * eapply Weakae.
        1: apply ded.
        apply inc.
      * apply IHs1.
        apply int.
Qed.

(* Lemma 3 *)

(* Again I had a lot of problems to find the right induction *)

Lemma winterp_cfsm_refl A:
  ctx_winterp cut_free_syntactic_model A A.
Proof.
  remember A as A' eqn : ha.
  rewrite ha at 2.
  induction A in A', ha |-*.
  - constructor.
  - split.
    + apply Correctness.
      rewrite ha.
      apply AEAsm.
      now left.
    + destruct A'.
      * inversion ha.
      * eapply ctx_monotonicity.
        1: apply incl_cons'.
        apply IHA.
        now inversion ha.
Qed.

(* Theorem 4 *)

Theorem cut_elim A s:
  (forall M w, ctx_winterp M w A -> winterp M w s) ->
  cf A s.
Proof.
  intro soundness.
  apply Correctness.
  apply soundness.
  apply winterp_cfsm_refl.
Qed.

(* Lemma 5 *)

Lemma not_ae_wtht_hyp s:
  ~ (ae [] s).
Proof.
  intro.
  remember [] as A eqn:h.
  induction H.
  - rewrite h in H.
    inversion H.
  - apply (IHae h).
Qed.

(* unfolding function *)

Fixpoint unfld A s:=
  match A with 
  | [] => s
  | t::A => t ~> unfld A s
  end.


Notation "A --> s" := (unfld A s) (at level 70).

(* Lemma 6 *)

(* Travis helped there to get the right generalization *)
(* Little design choice: as someone suggested it on the Discord server,
   I started to use revert instead a,b |-*. 
   I find this process much clearer and it permits me to understand a bit 
   better how the induction actually works in Rocq. *)

Lemma six A:
  let s := var 0 in ~ (ae [neg (neg s)] (A --> s)).
Proof.
  intros s ded.
  remember [neg (neg s)] as A' eqn:ha.
  remember (A --> s) as s' eqn:hs.
  revert ha.
  revert hs.
  revert A.
  induction ded.
  - intros.
    subst.
    destruct A0.
    + simpl in H.
      destruct H.
      * inversion H.
      * apply H.
    + simpl in H.
      destruct H.
      * simpl in H.
        injection H.
        intros.
        destruct A0.
        {
          simpl in H0.
          discriminate H0.
        }
        simpl in H0.
        discriminate H0.
      * apply H.
  - intros.
    subst.
    apply (IHded (s0 :: A0)).
    all: reflexivity.
Qed.

(* Theorem 7 *)

Theorem dne_consistent:
  ~(forall s, [] |-m dne s).
Proof.
  intro h.
  specialize (h (var 0)).
  assert (cf [] (dne (var 0))).
  {
    apply cut_elim.
    intros.
    eapply wsoundness.
    - apply h.
    - apply H.
  }
  remember [] as A eqn:ha.
  remember (dne (var 0)) as f eqn:hf.
  revert ha.
  revert hf.
  destruct H.
  - intros.
    inversion hf.
    subst.
    eapply six with (A:= []).
    inversion H.
    subst.
    apply H0.
  - intros.
    subst.
    eapply not_ae_wtht_hyp.
    apply H.
Qed.

