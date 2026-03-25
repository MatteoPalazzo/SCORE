From Coq Require Import List.
Import ListNotations.

From CDF Require Import CommonDefinitions SCORE_language SCORE_interpreter SCORE_wellformedness_properties.
From CDF Require Import SCORE_interpreter_invertible_base_cases.
From CDF Require Import SCORE_interpreter_invertible_SEQ_case.
From CDF Require Import SCORE_interpreter_invertible_FOR_case.
Require Import Coq.Logic.FunctionalExtensionality.

Lemma example :
  forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Proof.
  intros A B f g H.
  apply functional_extensionality.
  exact H.
Qed.

(* From CDF Require Import SCORE_interpreter_invertible_FOR_case. *)

From Coq Require Import FunctionalExtensionality.

Open Scope SCORE_scope.

Lemma SEQ_assoc: forall P1 P2 P3 P4 s,
  eval ((P1 ;; P2) ;; P3 ;; P4) s
    = eval P4 (eval (P2 ;; P3) (eval P1 s)).
Proof. auto. Qed.

Theorem score_reversibility :
  forall (P : com),
    (wfcom P) ->
      (forall (s : store) (z : ident), eval (P ;; inv P) s z = s z /\ eval (inv P ;; P) s z = s z) .
Proof.
induction P.
1-5: intros; split.
+ exact (SKIP_inv_SKIP_id s z).
+ exact (inv_SKIP_SKIP_id s z).
+ exact (PUSH_inv_PUSH_id s x z).  
+ exact (inv_PUSH_PUSH_id s x z).
+ exact (POP_inv_POP_id s x z).
+ exact (inv_POP_POP_id s x z).
+ exact (DEC_inv_DEC_id s x z).
+ exact (inv_DEC_DEC_id s x z).
+ exact (INC_inv_INC_id s x z).
+ exact (inv_INC_INC_id s x z).
+ intros.
  unfold wfcom in H. fold wfcom in H.
  destruct H.
  specialize (IHP1 H).
  specialize (IHP2 H0).
  unfold inv. fold inv.
  repeat rewrite SEQ_assoc.
  assert (forall (s : store) (z : ident), eval (P1;; inv P1) s z = s z).
  { intros. exact (proj1 (IHP1 s0 z0)). }
  assert (forall (s : store) (z : ident), eval (inv P1;; P1) s z = s z). 
  { intros. exact (proj2 (IHP1 s0 z0)). }
  assert (forall (s : store) (z : ident), eval (P2;; inv P2) s z = s z).
  { intros. exact (proj1 (IHP2 s0 z0)). }
  assert (forall (s : store) (z : ident), eval (inv P2;; P2) s z = s z).
  { intros. exact (proj2 (IHP2 s0 z0)). }
  split.
  ++ assert ((eval (P2;; inv P2) (eval P1 s)) = (eval P1 s)).
     { apply functional_extensionality.
       intro. exact (H3 (eval P1 s) x). }
     rewrite H5.
     unfold eval in H1; fold eval in H1. 
     exact (H1 s z).
  ++ assert (eval (inv P1;; P1) (eval (inv P2) s) = (eval (inv P2) s)).
     { apply functional_extensionality.
       intro. exact (H2 (eval (inv P2) s) x). }
     rewrite H5.
     unfold eval in H1; fold eval in H1. 
     exact (H4 s z).
+ exact (FOR_inv_FOR_id P IHP x).
Qed.

(* Corollary score_reversibility_inv :
    forall (P : com) (s : store),
    (wfcom P) ->
      (eval (inv P ;; P) s = s) .
Proof.
intros.
assert (inv (inv P) = P) as HInvInvP. {
  exact (inv_self_dual P).
}
rewrite wfcom_inv in H.
rewrite <- HInvInvP at 2.
apply (score_reversibility (inv P) H s).
Qed. *)

