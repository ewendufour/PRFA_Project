From Stdlib Require Import List.
Import ListNotations.
Inductive form : Type :=
| var ( x : nat) | bot | imp ( s t : form).
Print In.
Print incl.
Notation "s ~> t" := (imp s t) ( at level 51, right associativity).
Notation neg s := ( imp s bot).
Reserved Notation "A ⊢c s" (at level 70).


(* For handling administrative steps *)
Lemma In_hd :
  forall A (x : A) l,
    In x (x :: l).
Proof.
  intros.
  unfold In.
  auto.
Qed.

Lemma In_tl :
  forall A (x y : A) l,
    In x l ->
    In x (y :: l).
Proof.
  intros.
  unfold In.
  auto.
Qed.

Lemma In_eq : 
  forall A (x y :A) l,
  x = y -> In x (y::l) .
Proof.
  intros A x y l.
  induction 1.
  apply In_hd.
Defined.


Create HintDb indb.
Hint Resolve In_hd : indb.
Hint Resolve In_tl : indb.
Hint Resolve In_eq : indb.
(* END *)

(* ex 1.1 *)

(* ex 1.1.a *)

Inductive ndc : list form -> form -> Prop:=
  | CAsm A s: In s A -> ndc A s
  | CImp A s t: ndc (s::A) t -> ndc A (s ~> t) 
  | CMP A s t: ndc A (imp s t) -> ndc A s -> ndc A t
  | CCont A s: ndc (neg s::A) bot -> ndc A s.

Notation "A |-c s" := (ndc A s) (at level 70).

(* ex 1.1.b *)

Goal forall A s, A |-c s ~> s.  
Proof.
  intros A s.
  apply CImp.
  apply CAsm.
  auto with indb.
Qed.

Goal forall A s, s::A |-c neg (neg s).
Proof.
  intros A c.
  apply CImp.
  eapply CMP.
  - eapply CAsm.
    auto with indb.
  - apply CAsm.
    auto with indb.
Qed.

Goal [neg (neg bot)] |-c bot.
Proof.
  apply CMP with (s := neg bot).
  + apply CAsm.
    auto with indb.
  + apply CImp.
    apply CAsm.
    auto with indb.
Qed.

Goal forall A s, A |-c (neg (neg s)) ~> s.
Proof.
  intros A s.
  apply CImp.
  apply CCont.
  apply CMP with (s := (neg s)).
  - apply CAsm.
    auto with indb.
  - apply CAsm.
    auto with indb.
Qed.

(* ex 1.1.c *)

Lemma add_head_incl {A} (x:A) (l l':list A):
 incl l l' -> incl (x::l) (x::l').
Proof.
  intros h y h'.
  specialize (h y).
  destruct h'.
  - rewrite H.
    auto with indb.
  - right.
    apply (h H).
Qed.

(* I had some difficulties finding the right induction and generalization *)

Fact Weakc A B s:
  A |-c s -> incl A B -> B |-c s.
Proof.
  intros hd.
  induction hd in B |- *.
  - intro hincl.
    apply CAsm.
    specialize (hincl s) as hs.
    apply (hs H).
  - intro hincl.
    apply CImp.
    apply IHhd.
    apply add_head_incl.
    exact hincl.
  - intro hincl.
    apply CMP with (s:= s).
    + apply (IHhd1 B hincl).
    + apply (IHhd2 B hincl).
  - intro hincl.
    apply CCont. 
    apply IHhd. 
    apply add_head_incl.
    exact hincl.
Qed.
    
(* ex 1.1.d *)

Inductive ground : form -> Prop:=
| Gbot : ground bot
| Gimp s t: ground s -> ground t -> ground (s ~> t).

(* ex 1.2 *)

Definition model:= nat -> Prop.

(* ex 1.2.a *)



Fixpoint interp (M:model) (f:form) : Prop :=
  match f with 
  | bot => False
  | s ~> t => (interp M s) -> (interp M t)
  | var k => M k
  end.


(* ex 1.2.b *)

Fixpoint ctx_interp (M:model) (A:list form) :=
  match A with 
  | [] => True
  | f :: l => interp M f /\ ctx_interp M l
  end.

(* ex 1.2.c *)

(* Again, I had some difficulties to find the right induction *)

Lemma soundness M A (s:form):
  (forall P, ~~P -> P) ->
    A |-c s ->
    ctx_interp M A ->
    interp M s.
Proof.
  intros dne ded int.
  induction ded.
  - induction A.
    + inversion H.
    + destruct H.
      * rewrite H in int.
        destruct int as [hs _].
        apply hs.
      * destruct int as [_ hA].
        apply (IHA H hA).
  - simpl.
    intro.
    apply IHded.
    split.
    + apply H.
    + apply int.
  - simpl in IHded1. 
    apply (IHded1 int (IHded2 int)).
  - simpl in IHded.
    apply dne.
    intro.
    apply IHded.
    split.
    + exact H.
    + exact int.
Qed.

(* ex 1.2.d *)

Lemma classical_consistency:
  (forall P, ~~P -> P) ->
  ~ ([] |-c bot).
Proof.
  intros dne der.
  apply (soundness (fun _ => False) [] bot dne der).
  simpl.
  constructor.
Qed.

(* ex 1.2.e *)

Lemma constructive_soundness (M:model) (A: list form) (s:form):
  A |-c s -> ctx_interp M A-> ~~ interp M s.
Proof.
  intros ded int nint.
  induction ded.
  - induction A.
    + inversion H.
    + destruct H.
      * destruct int as [intl _].
        rewrite H in intl.
        apply (nint intl). 
      * destruct int as [_ intr].
        apply (IHA H intr).
  - apply nint.
    simpl.
    intro.
    exfalso.
    apply IHded.
    + simpl.
      split.
      * apply H.
      * apply int.
    + intro.
      apply nint.
      simpl.
      intro.
      apply H0.
  - apply IHded1.
    + apply int.
    + intro.
      apply IHded2.
      * apply int.
      * intro.
        apply nint.
        simpl in H.
        apply H.
        apply H0.
  - apply IHded.
    + split.
      * simpl. 
        intro.
        apply (nint H).
      * apply int.
    + intro.
      apply H.
Qed.

(* ex 1.2.f *)

Lemma constructive_consistency:
  ~([] |-c bot).
Proof.
  intro ded.
  apply (constructive_soundness (fun _ => False) [] bot ded).
  - constructor.
  - intro. inversion H.
Qed.
