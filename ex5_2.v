From Stdlib Require Import List.
From Project Require Import ex5_1.
Import ListNotations.

(* ex 2.1 *)
(* ex 2.1.a *)

Inductive ndm : list form -> form -> Prop:=
  | MAsm A s: In s A -> ndm A s
  | MImp A s t: ndm (s::A) t -> ndm A (s ~> t) 
  | MMP A s t: ndm A (imp s t) -> ndm A s -> ndm A t
  | MAndI A s t: ndm A s -> ndm A t -> ndm A (and s t)
  | MAndE1 A s t: ndm A (and s t) -> ndm A s
  | MAndE2 A s t: ndm A (and s t) -> ndm A t
.

Notation "A |-m s" := (ndm A s) (at level 70).


(*ex 2.1.b *)

Lemma Weakm (A B: list form) (s:form) :
  A |-m s -> incl A B -> B |-m s.
Proof.
  intro ded.
  induction ded in B |-*.
  - intro inc.
    apply inc in H.
    apply MAsm. 
    apply H.
  - intro inc. 
    apply MImp. 
    apply IHded.
    apply add_head_incl.
    apply inc.
  - intro incl.
    simpl in IHded1.
    apply MMP with (s:=s).
    + apply (IHded1 B incl).
    + apply (IHded2 B incl).
  - intro incl.
    apply MAndI.
    + apply IHded1.
      apply incl.
    + apply IHded2.
      apply incl.
  - intro.
    eapply MAndE1.
    apply IHded.
    apply H.
  - intro.
    eapply MAndE2.
    apply IHded.
    apply H.
Qed.

(* ex 2.1.c *)

Lemma Implication (A : list form) (s : form) :
  A |-m s -> A |-c s.
Proof.
  induction 1.
  - apply CAsm.
    apply H.
  - apply CImp.
    apply IHndm.
  - apply CMP with (s:=s).
    all: assumption.
  - apply CAndI.
    all: assumption.
  - eapply CAndE1.
    eassumption.
  - eapply CAndE2.
    eassumption.
Qed.

(* ex 2.1.d *)

Fixpoint trans (t :form) (s:form) : form :=
  match s with 
  | bot => t
  | var x => (var x ~> t) ~> t
  | u ~> v => trans t u ~> trans t v
  | and u v => and (trans t u) (trans t v)
  end.

(* ex 2.1.e *)

Lemma DNE_Friedman (A:list form) (s t:form) :
  A |-m ((trans t s ~> t) ~> t) ~> (trans t s).
Proof.
  induction s in A|-*.
  all: apply MImp.
  all: simpl.
  - apply MImp.
    eapply MMP.
    + apply MAsm.
      right.
      left.
      reflexivity.
    + apply MImp.
      eapply MMP.
      all: apply MAsm.
      * now left.
      * right.
        now left.
  - eapply MMP.
    + apply MAsm.
      now left.
    + apply MImp.
      apply MAsm.
      now left.
  - apply MImp.
    eapply MMP.
    + apply IHs2.
    + apply MImp. 
      eapply MMP. 
      * apply MAsm.
        right. 
        right.
        now left.
      * apply MImp.
        eapply MMP.
        {
          apply MAsm.
          right.
          now left.
        }
        eapply MMP.
        {
          apply MAsm.
          now left.
        }
        apply MAsm.
        right. right.
        now left.
  - apply MAndI.
    + eapply MMP.
      * apply IHs1.
      * apply MImp.
        eapply MMP.
        {
          apply MAsm.
          right.
          now left.
        }
        {
          apply MImp.
          eapply MMP.
          - apply MAsm.
            right.
            now left.
          - eapply MAndE1.
            apply MAsm.
            now left.
        }
    + eapply MMP.
      * apply IHs2.
      * apply MImp.
        eapply MMP.
        {
          apply MAsm.
          right.
          now left.
        }
        {
          apply MImp.
          eapply MMP.
          - apply MAsm.
            right.
            now left.
          - eapply MAndE2.
            apply MAsm.
            now left.
        }
Qed.

(* ex 2.1.f *)

Lemma In_map {A B} (l:list A) (f: A -> B) x: 
  In x l -> In (f x) (map f l).
Proof.
  intros.
  induction l.
  - inversion H.
  - simpl.
    induction H.
    + left.
      now rewrite H.
    + right. 
      apply (IHl H).
Qed.

Lemma Friedman (A:list form) (s t:form):
  A |-c s -> map (trans t) A |-m trans t s.
Proof.
  induction 1.
  - apply MAsm.
    apply In_map.
    exact H.
  - simpl.
    apply MImp.
    simpl in IHndc.
    apply IHndc.
  - simpl in IHndc1.
    eapply MMP.
    + apply IHndc1.
    + apply IHndc2.
  - simpl in IHndc.
    apply MImp in IHndc.
    eapply MMP.
    + apply DNE_Friedman.
    + apply IHndc.
  - simpl.
    apply MAndI.
    all: assumption.
  - eapply MAndE1.
    eassumption.
  - eapply MAndE2.
    eassumption.
Qed.

(* ex 2.1.g *)

Lemma ground_trans (s:form) :
  ground s -> s = trans bot s.
Proof.
  intro.
  induction s.
  - inversion H.
  - reflexivity.
  - simpl.
    inversion H.
    rewrite <- (IHs1 H2).
    now rewrite <- (IHs2 H3).
  - simpl.
    inversion H.
    subst.
    rewrite <- (IHs1 H2).
    now rewrite <- (IHs2 H3).
Qed.

Lemma ground_truths (s:form) :
  ground s -> ([] |-m s <-> [] |-c s).
Proof.
  intro gs.
  split.
  - apply Implication.
  - intro.
    induction s.
    + inversion gs.
    + apply constructive_consistency in H.
      inversion H.
    + apply Friedman with (t:=bot) in H.
      simpl in H.
      inversion gs.
      rewrite <- (ground_trans s1 H2) in H.
      rewrite <- (ground_trans s2 H3) in H.
      assumption.
    + inversion gs.
      subst.
      apply MAndI.
      * apply IHs1.
        apply H2.
        eapply CAndE1.
        apply H.
      * apply IHs2.
        apply H3.
        eapply CAndE2.
        apply H.
Qed.

(* ex 2.1.h *)
Lemma consistent_iff:
  [] |-m bot <-> [] |-c bot.
Proof.
  apply ground_truths.
  constructor.
Qed.

(* ex 2.1.i *)

Definition dne s := ((s ~> bot) ~> bot) ~> s.

Lemma consistency_of_dne (s: form):
  ~ ([] |-m (dne s) ~> bot).
Proof.
  intro.
  apply Implication in H.
  apply constructive_consistency.
  eapply CMP.
  - apply H.
  - apply CImp.
    apply CCont.
    eapply CMP.
    all: apply CAsm.
    + right.
      now left.
    + now left.
Qed.


(* ex 2.2.a *)

Record WModel := {
  world : Type;
  mbot : world -> Prop;
  inter : world -> nat -> Prop; 
  rel : world -> world -> Prop;
  rel_refl : forall (w : world), rel w w;
  rel_trans: forall (u v w: world), rel u v -> rel v w -> rel u w;
  rel_bot: forall (w w':world), (rel w w' /\ mbot w ) -> mbot w';
  rel_inter: forall (w w':world) (n:nat), (rel w w'/\ inter w n) -> inter w' n
}.

Notation "w '<=(' M ) w'" := (M.(rel) w w') (at level 40, w' at next level).

(* ex 2.2.b *)

Fixpoint winterp (M:WModel) (w : M.(world)) (s:form) : Prop:=
  match s with
  | bot => M.(mbot) w
  | t ~> u => forall w', (M.(rel) w w' /\ winterp M w' t) -> winterp M w' u
  | var n => M.(inter) w n
  | and t u => winterp M w t /\ winterp M w u
  end.

(* ex 2.2.c *)

Fixpoint ctx_winterp (M:WModel) (w: M.(world)) (A:list form) : Prop :=
  match A with
  | [] => True
  | a::A' => winterp M w a /\ ctx_winterp M w A'
  end.

(* ex 2.2.d *)

Lemma monotonicity (M:WModel) (s:form) (w w':M.(world)) :
  w <=(M) w' -> winterp M w s -> winterp M w' s.
Proof.
  intro hr.
  induction s.
  all: simpl.
  all: intro hint.
  - eapply rel_inter.
    split.
    + apply hr.
    + apply hint.
  - eapply rel_bot.
    split.
    + apply hr.
    + apply hint.
  - intros w0 [hr' hwi].
    apply hint.
    split.
    + eapply rel_trans.
      * apply hr.
      * apply hr'.
    + apply hwi.
  - destruct hint.
    split.
    + apply IHs1.
      assumption.
    + apply IHs2.
      assumption.
Qed.

(* ex 2.2.e *)

Lemma ctx_monotonicity M A w w':
  w <=(M) w' -> ctx_winterp M w A -> ctx_winterp M w' A.
Proof.
  intro hr.
  induction A.
  - intro.
    constructor.
  - simpl.
    intros [hia hiA].
    split.
    + eapply monotonicity.
      * apply hr.
      * apply hia.
    + apply (IHA hiA).
Qed.

(* ex 2.2.f*)
Lemma interp_all_elements M w A s:
  In s A -> ctx_winterp M w A -> winterp M w s.  
Proof.
  induction A.
  - intro H.
    inversion H.
  - intros Hin [hia hiA].
    induction Hin.
    + congruence.
    + apply IHA.
      * apply H.
      * apply hiA.
Qed.


Lemma wsoundness M A s:
  A |-m s -> forall (w : M.(world)), ctx_winterp M w A -> winterp M w s.
Proof.
  induction 1.
  all: intros.
  - eapply interp_all_elements.
    + apply H.
    + apply H0.
  - simpl.
    intros w' [hr hw's].
    apply IHndm.
    eapply ctx_monotonicity in H0.
    + split.
      * apply hw's.
      * apply H0.
    + apply hr.
  - simpl in IHndm1.
    eapply IHndm1.
    + apply H1.
    + split.
      * apply rel_refl.
      * apply IHndm2.
        apply H1.
  - simpl.
    split.
    + apply IHndm1.
      assumption.
    + apply IHndm2.
      assumption.
  - apply IHndm.
    assumption.
  - apply IHndm.
    assumption.
Qed.

(* ex 2.2.g *)

Definition consistency_model : WModel.
Proof.
  refine {| world := unit; mbot := (fun x => False); inter := (fun _ _ => True); rel := (fun _ _ => True)|}.
  all: intros.
  1-2: constructor.
  2: constructor.
  destruct H as [ _ hF].
  inversion hF.
Defined.

(* ex 2.2.h *)

Lemma consistency:
  ~ ([] |-m bot).
Proof.
  intro .
  eapply wsoundness with (M := consistency_model) (w:= tt) in H.
  - simpl in H.
    assumption.
  - constructor.
Qed.

(* ex 2.2.i *)

Definition notdne_model : WModel.
Proof.
  refine 
    {| 
      world := bool;
      mbot:= (fun _ => False);
      inter := 
        (fun w _ => match w with 
                    | true => True
                    | false => False
                    end);
      rel := 
        (fun w w' => match w, w' with 
                     | true, false => False
                     | _, _ => True
                     end)
    |}.
  - destruct w.
    all: constructor.
  - destruct u.
    all: destruct v.
    1-3: destruct w.
    all: intros.
    all: try constructor.
    all: assumption.
  - intros _ _ [_ F].
    assumption.
  - intros w w' n.
    destruct w.
    + intros [h _].
      assumption.
    + intros [_ F].
      inversion F.
Defined.

(* ex 2.2.j *)
Lemma dne_independant:
  ~(forall s, []|-m dne s).
Proof.
  intro h.
  specialize (h (var 0)).
  eapply wsoundness with (M:=notdne_model) in h.
  - simpl in h.
    specialize (h false).
    simpl in h.
    apply h.
    clear.
    split.
    + instantiate (1:=false).
      constructor.
    + intros w' [_ h].
      eapply h.
      destruct w'.
      * instantiate (1:= true).
        simpl.
        split.
        all: constructor.
      * split.
        all : constructor.
  - constructor.
Qed.

(* ex 2.3.a *)

Definition syntactic_model : WModel.
Proof.
  refine {|
    world := list form;
    mbot := fun A => A|-m bot;
        inter := fun A n => A |-m var n;
    rel := @incl form
  |}.
  - apply incl_refl.
  - apply incl_tran.
  - intros w w' [inc ded].
    eapply Weakm.
    + apply ded.
    + apply inc.
  - intros w w' n [inc ded].
    eapply Weakm.
    + apply ded.
    + apply inc.
Defined.

(* ex 2.3.b *)

Lemma incl_cons' {A} (l: list A) x:
  incl l (x::l).
Proof. 
  intros x' h.
  right.
  apply h.
Qed.


Lemma correctness A s:
  winterp syntactic_model A s <-> A|-m s.
Proof.
  induction s in A|-*.
  - now simpl.
  - now simpl.
  - simpl.
    split.
    + intro.
      apply MImp.
      specialize (H (s1::A)).
      apply IHs2.
      apply H.
      split.
      * apply incl_cons'.
      * apply IHs1.
        apply MAsm.
        now left.
    + intros ded w' [inc int].
      apply IHs2.
      eapply MMP.
      eapply Weakm.
      apply ded.
      apply inc.
      apply IHs1.
      apply int.
  - split.
    + intro.
      apply MAndI.
      * apply IHs1.
        apply H.
      * apply IHs2.
        apply H.
    + intro.
      split.
      * apply IHs1.
        eapply MAndE1.
        apply H.
      * apply IHs2.
        eapply MAndE2.
        apply H.
Qed.


(* ex 2.3.c *)

Lemma ctx_winterp_syntactic_refl A:
  ctx_winterp syntactic_model A A.
Proof.
  induction A.
  - now simpl.
  - split.
    + apply correctness.
      apply MAsm.
      now left.
    + eapply ctx_monotonicity.
      * instantiate (1:=A).
        simpl.
        apply incl_cons'.
      * apply IHA.
Qed.


Lemma completness A s:
  (forall M w, ctx_winterp M w A -> winterp M w s) -> A |-m s.
Proof.
  intro h.
  apply correctness.
  apply h.
  apply ctx_winterp_syntactic_refl.
Qed.
  
