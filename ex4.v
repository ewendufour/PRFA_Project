From Project Require Import ex1.
From Project Require Import ex2.
From Stdlib Require Import Lia ZArith List.
Import ListNotations.

(* ex 4.1.a *)

Inductive hil (A :list form) : form -> Prop:=
| HAsm s : In s A -> hil A s
  | HMP s t: hil A (s~>t) -> hil A s -> hil A t
  | HAx1 s t: hil A (s~>t~>s)
  | HAx2 s t u: hil A ((s ~>t ~> u ) ~> (s ~> t) ~> s ~> u).

Notation "A |-H s":=(hil A s) (at level 70).

(* ex 4.1.b *)

Lemma hil_ndm A s:
  A |-H s -> A |-m s.
Proof.
  induction 1.
  - apply MAsm.
    apply H.
  - eapply MMP.
    apply IHhil1.
    apply IHhil2.
  - repeat apply MImp.
    apply MAsm.
    right.
    now left.
  - repeat apply MImp.
    eapply MMP.
    + eapply MMP.
      * apply MAsm.
        do 2 right.
        now left.
      * apply MAsm.
        now left.
    + eapply MMP.
      * apply MAsm.
        right.
        now left.
      * apply MAsm.
        now left.
Qed.

(* ex 4.1.c *)

Fact f1 A s t:
  A |-H s -> A |-H t ~> s.
Proof.
  intro de.
  eapply HMP.
  - apply HAx1.
  - apply de.
Qed.

Fact f2 A s t u:
  A |-H (s ~> t ~> u) -> A |-H (s ~> t) -> A |-H s ~>u.
Proof.
  intros.
  eapply HMP.
  - eapply HMP.
    + eapply HAx2.
    + apply H.
  - apply H0.
Qed.

(* I had some difficulties to find the right formula for applying the MP rule *)
Fact f3 A s:
  A |-H s ~> s.
Proof.
  eapply HMP.
  - eapply HMP.
    + eapply HAx2.
    + apply HAx1.
  - instantiate (1:= s ~> s).
    apply HAx1.
Qed.

(* ex 4.1.d *)

Lemma hil_imp_intro A s t:
  s::A |-H t -> A |-H s ~> t.
Proof.
  intro.
  induction H.
  - induction H.
    + subst.
      apply f3.
    + apply f1.
      apply HAsm.
      apply H.
  - eapply f2.
    + apply IHhil1.
    + apply IHhil2.
  - apply f1.
    apply HAx1.
  - apply f1.
    apply HAx2.
Qed.

(* ex 4.1.e *)
Lemma ndm_hil A s:
  A |-m s -> A |-H s.
Proof.
  induction 1.
  - apply HAsm.
    apply H.
  - apply hil_imp_intro.
    apply IHndm.
  - eapply HMP.
    + apply IHndm1.
    + apply IHndm2.
Qed.


(* ex 4.2 *)

Section ARS.

  Context {A:Type} (R:A -> A -> Prop). 

  (* ex 4.2.a *)
  Inductive SN_on R: A -> Prop:=
    | RPath x:(forall y, R x y -> SN_on R y) -> SN_on R x.

  (* ex 4.2.b *)

  Inductive rtc : A -> A -> Prop  :=
    | Refl x: rtc x x
    | Trans x y z: rtc x y -> rtc y z -> rtc x z
    | Star x y: R x y -> rtc x y.
  
  (* ex 4.2.c *)
  
  Lemma SN_on_rtc x y:
    SN_on R x -> rtc x y -> SN_on R y.
  Proof.
    induction 2.
    - apply H.
    - apply IHrtc2.
      apply IHrtc1.
      apply H.
    - inversion H.
      apply H1.
      apply H0.
  Qed.

  (* ex 4.2.d *)

  Variables T V : A -> Prop.

  Variable Hpres: forall x y, T x -> R x y -> T y.
  Variable Hprog: forall x, T x -> (exists y, R x y) \/ V x. 

  Lemma SN_to_WN x:
    T x -> SN_on R x -> exists v, rtc x v /\ T v /\ V v.
  Proof.
    intro tx.
    induction 1 as [x h ind].
    specialize (Hprog x tx) as [rxy | vx].
    - destruct rxy as [y rxy].
      specialize (ind y).
      specialize (Hpres x y tx rxy) as ty.
      specialize (Star x y rxy) as rtcxy.
      specialize (h y rxy) as sny. 
      destruct (ind rxy ty) as [v hv].
      exists v.
      destruct hv as [rtcyv [tv Vv]].
      split.
      eapply Trans.
      + apply rtcxy.
      + apply rtcyv.
      + split.
        * apply tv.
        * apply Vv.
    - exists x.
      split.
      + constructor.
      + split.
        * apply tx.
        * apply vx.
  Qed.

End ARS.

(* ex 4.2.e *)

(* I got stuck for a long time and tried this proof on paper.
   Tianwen gave me an hint on what to revert in the proof *)

Lemma SN_on_double_ind [A B:Type] [R1 : A -> A -> Prop] [R2: B -> B -> Prop]
  (P : A -> B -> Prop) :
  (forall (a:A) (b:B),
    (forall (a':A), R1 a a' -> SN_on R1 a') ->
    (forall (a':A), R1 a a' -> P a' b) ->
    (forall (b':B), R2 b b' -> SN_on R2 b') ->
    (forall (b':B), R2 b b' -> P a b') -> P a b) ->
  forall (x:A) (y:B), SN_on R1 x -> SN_on R2 y -> P x y.
Proof.
  intros h x y snx.
  revert y.
  induction snx as [x snx' px'].
  intros y sny.
  induction sny as [y sny' py'].
  apply h.
  - apply snx'.
  - intros x' rxx'.
    apply px'.
    + apply rxx'.
    + constructor.
      apply sny'.
  - apply sny'.
  - apply py'.
Qed.
  
  
    
Inductive term:=
  | S | K | V (n : nat) | app (e1 e2 : term).

Coercion app: term >-> Funclass.

Section typing.
  Variable A : list form.

  Reserved Notation "|- e : s" (at level 60, e at next level).


  (* ex 4.3.a *)

  Inductive typing : term -> form -> Prop:=
    | tV n s: (nth_error A n = Some s) -> (typing (V n) s)
    | tapp e1 e2 s t: typing e1  (s ~> t) -> typing  e2  s -> typing (e1 e2) t
    | tK s t: typing K (s ~> t ~> s)
    | tS s t u: typing S ((s ~> t ~> u) ~> (s~>t) ~> s ~> u).

  Notation "|- e : s":=(typing e s) (at level 60, e at next level).

  (* ex 4.3.b *)

  Lemma hil_equiv s:
    A |-H s <-> exists e, |- e : s.
  Proof.
    split.
    - induction 1.
      + specialize (In_nth_error A s H) as [n hn].
        exists (V n).
        apply tV.
        apply hn.
      + destruct IHhil1 as [e1 te1].
        destruct IHhil2 as [e2 te2].
        exists (e1 e2).
        eapply tapp.
        * apply te1.
        * apply te2.
      + exists K.
        apply tK.
      + exists S.
        apply tS.
    - intros [e te].
      induction te.
      + apply HAsm.
        eapply nth_error_In.
        apply H.
      + eapply HMP.
        * apply IHte1.
        * apply IHte2.
      + apply HAx1.
      + apply HAx2.
  Qed.

  (* ex 4.3.c *)

  Inductive red : term -> term -> Prop:=
    | rK e1 e2: red (K e1 e2) e1
    | rS e1 e2 e3: red (S e1 e2 e3) (e1 e3 (e2 e3))
    | lapp e1 e1' e2: red e1 e1' -> red (e1 e2) (e1' e2)
    | rapp e1 e2 e2': red e2 e2' -> red (app e1 e2) (app e1 e2').


  Notation "e1 ≻ e2":=(red e1 e2) (at level 60).

  (* ex 4.3.d *)

  Lemma preservation e1 e2 s:
    |- e1 : s -> e1 ≻ e2 -> |- e2 : s. 
  Proof.
    intros h re.
    revert h.
    revert s.
    induction re.
    all: intros s tp.
    all: inversion tp.
    - inversion H1.
      inversion H6.
      congruence.
    - inversion H1.
      inversion H6.
      inversion H11.
      subst.
      eapply tapp.
      + eapply tapp.
        * apply H13.
        * apply H3.
      + eapply tapp.
        * apply H8.
        * apply H3.
    - subst.
      eapply tapp.
      + apply IHre.
        apply H1.
      + apply H3.
    - subst.
      eapply tapp.
      + apply H1.
      + apply IHre.
        apply H3.
  Qed.

  (* ex 4.3.e *)

  Definition reds:=
    rtc red.

  Notation "e1 ≻* e2":=(reds e1 e2) (at level 60).

  Lemma app_red e1 e1' e2:
    e1 ≻* e1'-> e1 e2 ≻* e1' e2.
  Proof.
    induction 1.
    - apply Refl.
    - eapply Trans.
      + apply IHrtc1.
      + apply IHrtc2.
    - apply Star.
      apply lapp.
      apply H.
  Qed.

  (* ex 4.3.f *)

  Lemma subject_reduction e1 e2 s:
    |- e1 : s -> e1 ≻* e2 -> |-e2 :s .
  Proof.
    induction 2.
    - apply H.
    - apply IHrtc2.
      apply IHrtc1.
      apply H.
    - eapply preservation.
      + apply H.
      + apply H0.
  Qed.
End typing.


(* ex 4.3.g *)

Notation "A |- e : s":=(typing A e s) (at level 60, e at next level).

Notation "t1 ≻ t2":=(red t1 t2) (at level 60).
Notation "t1 ≻* t2":= (rtc red t1 t2) (at level 60).

Definition SN (e:term):=
  SN_on red e.

(* I disscussed with Travis because I was struggling again 
   to find the right induction *)
Lemma SN_app (e1 e2:term):
  SN (e1 e2) -> SN e1.
Proof.
  remember (e1 e2) as e eqn:he.
  intro.
  revert he.
  induction H in e1 |-*.
  intros.
  constructor.
  intros.
  eapply H0 with (y:= y e2).
  - rewrite he.
    apply lapp.
    apply H1.
  - reflexivity.
Qed.



(* ex 4.3.h *)

Definition neutral (e:term):=
  match e with 
  | app K _ | K | app (app S _) _ | S | app S _ => False
  | _ => True
  end.

Lemma neutral_app e1 e2:
  neutral e1 -> neutral (e1 e2).
Proof.
  intro ne1.
  destruct e1.
  - inversion ne1.
  - inversion ne1.
  - constructor.
  - simpl in ne1.
    simpl.
    assert (e1_1 <> S).
    {
      intro.
      subst.
      apply ne1.
    }
    destruct e1_1.
    all: try constructor.
    now apply H.
Qed.

(* ex 4.3.i *)

Lemma progress e s:
  ([] |- e : s) -> (exists e', red e e') \/ ~(neutral e).
Proof.
  revert s.
  induction e.
  all: intros s ty.
  - right.
    intro.
    apply H.
  - right.
    intro.
    apply H.
  - inversion ty.
    subst.
    destruct n.
    + inversion H0.
    + inversion H0.
  - inversion ty.
    subst.
    apply IHe1 in H1.
    destruct H1 as [[e1' re]| nne1].
    + left.
      exists (e1' e2).
      apply lapp.
      apply re.
    + apply IHe2 in H3.
      destruct H3 as [[e2' re]| nne2].
      * left.
        exists (e1 e2').
        apply rapp.
        apply re.
      * destruct e1.
        all: try auto.
        destruct e1_1.
        all: try auto.
        {
          left.
          exists e1_2.
          constructor.
        }
        {
          simpl in nne1.
          destruct e1_1_1.
          all: try auto.
          left.
          exists (e1_1_2 e2 (e1_2 e2)).
          constructor.
        }
Qed.

(* ex 4.4 *)

(* Definition 1 *)

Fixpoint typ (e :term) s:=
  match s with
  | bot => SN e 
  | var x => SN e
  | t ~> u => forall e', typ e' t -> typ (e e') u  
  end.

Notation "⊨ e : s":= (typ e s) (at level 60, e at next level).

(* Theorem 8 *)
(* I used the lemma below to split my IHs for them to be more convenient to use *)

Lemma separation {X:Type} (P1 P2: X -> Prop):
  (forall e, (P1 e) /\ (P2 e)) <-> (forall e, P1 e) /\ (forall e, P2 e).
Proof.
  split.
  - intro.
    split.
    all: intro e.
    all: specialize (H e).
    all: apply H.
  - intros [h1 h2] e.
    split.
    + apply (h1 e).
    + apply (h2 e).
Qed.


Theorem eight s e:
  ((typ e s ) -> SN e) /\
  ((typ e s) -> forall e',e ≻* e' -> typ e' s) /\
  (neutral e /\ (forall e', e ≻ e'-> typ e' s) -> typ e s).
Proof.
  Search "forall".
  induction s in e |-*.
  - split.
    + tauto.
    + split.
      * intros.
        eapply SN_on_rtc.
        1 :apply H.
        apply H0.
      * intros.
        simpl.
        constructor.
        destruct H as [_ h].
        apply h.
  - split.
    + tauto.
    + split.
      * intros. 
        eapply SN_on_rtc.
        1: apply H.
        apply H0.
      * intros.
        destruct H as [ _ h].
        simpl.
        constructor.
        apply h.
  - rewrite separation in IHs1.
    destruct IHs1 as [ihs11 IHs1].
    rewrite separation in IHs1.
    destruct IHs1 as [ihs12 ihs13].
    rewrite separation in IHs2.
    destruct IHs2 as [ihs21 IHs2].
    rewrite separation in IHs2.
    destruct IHs2 as [ihs22 ihs23].
    split.
    + simpl.
      intro h.
      apply SN_app with (e2:= (V 0)).
      apply ihs21.
      apply h.
      apply ihs13.
      split.
      * constructor.
      * intros.
        inversion H.
    + split.
      * simpl.
        intros h e' re e1 te1.
        eapply ihs22.
        {
          apply h.
          apply te1.
        }
        {
          apply app_red.
          apply re.
        }
      * intros [ne H] e1 te1.
        apply ihs11 in te1 as sne1.
        induction sne1 as [e1 h1e h2e].
        apply ihs23.
        split.
        1: apply neutral_app.
        1: apply ne.
        intros e' re.
        inversion re.
        all: subst.
        {
          inversion ne. 
        }
        {
          inversion ne.
        }
        {
          apply H.
          - apply H3.
          - apply te1.
        }
        {
          apply h2e.
          - apply H3.
          - eapply ihs12.
            + apply te1.
            + apply Star.
              apply H3.
        }
Qed.

(* Lemma 9 *)

Lemma nine s t:
  typ K (s ~> t ~> s).
Proof.
  intros e1 te1 e2 te2.
  specialize (eight s e1) as [sne1 [_ _]].
  specialize (sne1 te1).
  specialize (eight t e2) as [sne2 [_ _]].
  specialize (sne2 te2).
  revert te1.
  apply SN_on_double_ind with (x:= e1) (y:=e2) (R1:=red) (R2:=red).
  all: try assumption.
  intros.
  specialize (eight s (K a b)) as [ _ [ _ h]].
  apply h.
  split.
  - constructor.
  - intros e' re.
    inversion re.
    all: subst.
    + assumption.
    + inversion H6.
      all: subst.
      * inversion H7.
      * apply H0.
        1: apply H7.
        specialize (eight s a) as [_ [h' _]].
        apply h'.
        1: apply te1.
        apply Star.
        apply H7.
    + apply H2. 
      * apply H6.
      * apply te1.
Qed.

(* Lemma 10 *)

(* When you get the idea for the double ind, 
   the triple ind becomes easy *)

Lemma SN_on_triple_ind [A B C : Type] [R1 : A -> A -> Prop] [R2 : B -> B -> Prop] [R3 : C -> C -> Prop]
    (P : A -> B -> C -> Prop):
  (forall (a : A) (b : B) (c : C),
    (forall a' : A, R1 a a' -> SN_on R1 a') ->
    (forall a' : A, R1 a a' -> P a' b c) ->
    (forall b' : B, R2 b b' -> SN_on R2 b') ->
    (forall b' : B, R2 b b' -> P a b' c) -> 
    (forall c' : C, R3 c c' -> SN_on R3 c') ->
    (forall c' : C, R3 c c' -> P a b c') ->
    P a b c) ->
    forall (x : A) (y : B) (z : C), SN_on R1 x -> SN_on R2 y -> SN_on R3 z -> P x y z.
Proof.
  intros h x y z snx sny.
  revert sny.
  revert z.
  revert y.
  induction snx.
  eapply SN_on_double_ind.
  intros y z.
  intros.
  apply h.
  all: try auto.
  intros.
  eapply H0.
  - apply H5.
  - constructor.
    apply H1.
  - constructor.
    apply H3.
Qed.

Lemma ten s t u:
   typ S ((s ~> t ~> u) ~> (s ~> t) ~> s ~> u).
Proof.
  intros e0 t0 e1 t1 e2 t2.
  specialize (eight (s~>t~>u) e0) as [sn0 _].
  specialize (sn0 t0).
  specialize (eight (s~>t) e1) as [sn1 _].
  specialize (sn1 t1).
  specialize (eight (s) e2) as [sn2 _].
  specialize (sn2 t2).
  revert t2.
  revert t1.
  revert t0.
  apply SN_on_triple_ind with (x:= e0) (y:=e1) (z:=e2) (R1:=red) (R2:=red) (R3:=red).
  all:try assumption.
  - intros.
    specialize (eight u (S a b c)) as [_ [_ h]].
    apply h.
    split.
    + constructor.
    + intros e re.
      inversion re.
      all: subst.
      * apply t0.
        1: apply t2. 
        apply t1.
        apply t2.
      * inversion H8.
        all: subst.
        {
          inversion H9.
          all: subst.
          - inversion H10.
          - apply H0.
            + apply H10.
            + specialize (eight (s ~> t ~> u) a) as [ _ [h' _]].
              apply h'.
              * assumption.
              * apply Star.
                assumption.
            + assumption.
            + assumption.
        }
        {
          apply H2.
          - apply H9.
          - assumption.
          - specialize (eight (s ~> t) b) as [_ [h' _]].
            apply h'.
            + assumption.
            + apply Star.
              assumption.
          - assumption.
        }
      * apply H4.
        all: try assumption.
        specialize (eight s c) as [ _ [h' _]].
        apply h'.
        1: assumption.
        apply Star.
        assumption.
Qed.

(* Theorem 11 *)

Lemma eleven A e s:
  (forall n s, nth_error A n = Some s -> typ (V n) s ) ->
  (A |- e : s) -> typ e s.
Proof.
  intros.
  induction H0.
  - apply (H n s H0).
  - apply IHtyping1.
    apply IHtyping2.
  - apply nine.
  - apply ten.
Qed.

(* Lemma 12 *)

Lemma twelve e s:
  [] |- e : s -> SN e. 
Proof.
  intro.
  specialize (eight s e) as [h _].
  apply h.
  apply eleven with (A:=[]).
  - intros.
    rewrite nth_error_nil in H0.
    inversion H0.
  - apply H.
Qed.

(* Lemma 13 *)

Lemma thirteen e s:
  [] |- e : s -> (exists e', rtc red e e' /\ [] |- e' : s /\ ~(neutral e')). 
Proof.
  intro.
  apply SN_to_WN with (x:=e) (T:= (fun e => [] |- e : s)) (V:=fun e => ~(neutral e)).
  - intros.
    eapply subject_reduction.
    + apply H0.
    + apply Star.
      apply H1.
  - intros.
    eapply progress.
    apply H0.
  - assumption.
  - eapply twelve.
    apply H.
Qed.


(* ex 4.5 *)

(* ex 4.5.a *)

Lemma noterm e:
  ~( [] |- e : bot).
Proof.
  intro.
  apply thirteen in H.
  destruct H as [e' [h1 [h2 h3]]].
  destruct h3.
  destruct e'.
  - inversion h2.
  - inversion h2.
  - inversion h2.
    rewrite nth_error_nil in H0.
    inversion H0.
  - destruct e'1.
    + simpl.
      inversion h2.
      subst.
      inversion H1.
    + inversion h2.
      subst.
      inversion H1.
    + constructor.
    + destruct e'1_1.
      * inversion h2.
        subst.
        inversion H1.
        subst.
        inversion H2.
      * constructor.
      * constructor.
      * constructor.
Qed.

(* ex 4.5.b *)

Corollary nd_consistent :
  ~ [] |-m bot.
Proof.
  intro.
  apply ndm_hil in H.
  apply hil_equiv in H.
  destruct H as [e he].
  apply (noterm e he). 
Qed.

(* ex 4.5.c *)

Corollary ndc_consistent :
  ~ [] |-c bot.
Proof.
  intro.
  apply nd_consistent.
  apply consistent_iff.
  apply H.
Qed.



