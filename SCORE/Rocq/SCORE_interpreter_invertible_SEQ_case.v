From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
Import ListNotations.

From Coq Require Import FunctionalExtensionality.
From CDF Require Import CommonDefinitions.
(* From CDF Require Import Sequences. *)
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Check com_ind. *)

Open Scope SCORE_scope.

Lemma SEQ_inv_SEQ_id:
forall P:com,
(forall (s: store), 
   (eval (P;; inv P) s = s) ) ->
 forall Q:com,
 (forall (s: store), 
   (eval (Q;; inv Q) s = s)) ->
(forall (s: store), 
  (eval ((P;; Q);; inv (P;; Q)) s = s)).
Proof.
intros P HP Q HQ s.
unfold inv. fold inv.
unfold eval. fold eval. 
rewrite (eval_fold_SEQ Q (inv Q) (eval P s)). 
rewrite HQ.
rewrite (eval_fold_SEQ P (inv P) s).
rewrite HP.
reflexivity.
Qed.

(* Lemma SEQ_assoc: forall P1 P2 P3 P4 s,
  eval (P1 ;; P2 ;; P3 ;; P4) s
    = eval P4 (eval (P2 ;; P3) (eval P1 s)).
Proof. auto. Qed. *)

(*Lemma SEQ_inv_SEQ_id:
forall P1 P2 : com,
(wfcom P1 ->
 forall (s : store) (z : ident), eval (P1;; inv P1) s z = s z /\ eval (inv P1;; P1) s z = s z) ->
(wfcom P2 ->
 forall (s : store) (z : ident), eval (P2;; inv P2) s z = s z /\ eval (inv P2;; P2) s z = s z) ->
wfcom (P1;; P2) ->
forall (s : store) (z : ident),
eval ((P1;; P2);; inv (P1;; P2)) s z = s z /\ eval (inv (P1;; P2);; P1;; P2) s z = s z.
Proof.
intros P Q IHP IHQ HwfcomP1P2 s z.
unfold wfcom in HwfcomP1P2. fold wfcom in HwfcomP1P2.
rewrite inv_unfold_SEQ.
assert (eval ((P ;; Q) ;; inv Q ;; inv P) s z = eval (inv P) (eval (Q ;; inv Q) (eval P s)) z) as HSeqAssoc1. { auto. }
assert (eval ((inv Q ;; inv P) ;; P ;;  Q) s z = eval (Q) (eval (inv P ;; P) (eval (inv Q) s)) z) as HSeqAssoc2. { auto. }
rewrite HSeqAssoc1.
rewrite HSeqAssoc2.
simpl.

rewrite eval_unfold_SEQ.
rewrite (eval_unfold_SEQ (inv (P;; Q)) (P;; Q)).
assert ()

unfold eval. fold eval. 
rewrite (eval_fold_SEQ Q (inv Q) (eval P s)).
rewrite (eval_fold_SEQ (inv P) P (eval (inv Q) s)).
destruct (HP (eval (inv Q) s)) as (HPl, HPr). 
destruct (HQ (eval P s)) as (HQl, HQr). 
rewrite HQl. rewrite HPr.
rewrite (eval_fold_SEQ P (inv P) s).
rewrite (eval_fold_SEQ (inv Q) Q s).
split.
- apply (proj1 (HP s)).
- apply (proj2 (HQ s)).
Qed.*)

(* Lemma SEQ_inv_SEQ_id:
forall P:com,
(forall (s: store), 
   (eval (P;; inv P) s = s) 
   /\ (eval (inv P;; P) s = s)) ->
 forall Q:com,
 (forall (s: store), 
   (eval (Q;; inv Q) s = s)
   /\ (eval (inv Q;; Q) s = s)) ->
(forall (s: store), 
  (eval ((P;; Q);; inv (P;; Q)) s = s)
  /\ (eval (inv (P;; Q);; (P;; Q)) s = s)).
Proof.
intros P HP Q HQ s.
unfold inv. fold inv.
unfold eval. fold eval. 
rewrite (eval_fold_SEQ Q (inv Q) (eval P s)).
rewrite (eval_fold_SEQ (inv P) P (eval (inv Q) s)).
destruct (HP (eval (inv Q) s)) as (HPl, HPr). 
destruct (HQ (eval P s)) as (HQl, HQr). 
rewrite HQl. rewrite HPr.
rewrite (eval_fold_SEQ P (inv P) s).
rewrite (eval_fold_SEQ (inv Q) Q s).
split.
- apply (proj1 (HP s)).
- apply (proj2 (HQ s)).
Qed. *)
