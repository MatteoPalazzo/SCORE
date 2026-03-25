From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
Import ListNotations.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import CommonDefinitions.
(* From CDF Require Import Sequences. *)
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter.
From CDF Require Import SCORE_interpreter_PUSH_POP_defs.
From CDF Require Import SCORE_interpreter_PUSH_POP_properties.
From CDF Require Import SCORE_reversibility_general_properties.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.


(*  
Check Z.iter.
Check Z_ind.
Check string_dec.
Search ({_ = _} + {_ <> _}). 
*)

(* Check com_ind. *)

Open Scope SCORE_scope.

(* SCORE is invertible: base cases *)

(* [SKIP] è l'inverso di [inv SKIP]. *)
Lemma SKIP_inv_SKIP_id: forall (s: store) (y: ident), 
  (eval (SKIP;; inv SKIP) s) y = s y.
Proof. intros. unfold inv. unfold eval. reflexivity.
Qed.

(* [inv SKIP] è l'inverso di [SKIP]. *)
Lemma inv_SKIP_SKIP_id: forall (s: store) (y: ident), 
  (eval (inv SKIP;; SKIP) s) y = s y.
Proof. intros. unfold inv. unfold eval. reflexivity.
Qed.

Lemma INC_DEC_id: forall s x y, 
  (eval (INC x ;; DEC x) s) y = s y.
Proof.
intros.
unfold eval.
rewrite update_same.
rewrite update_overwrite_var.
destruct (s x) as ((vx, px), cx) eqn:Hsx.
unfold fst. unfold snd.
assert (-1 + (1 + vx) = vx). { lia. }
rewrite H.
unfold update.
destruct (string_dec x y).
+ rewrite <- Hsx. rewrite e. reflexivity.
+ reflexivity.
Qed.

Lemma DEC_INC_id: forall s x y, 
  (eval (DEC x ;; INC x) s) y = s y.
Proof.
intros.
unfold eval.
rewrite update_same.
rewrite update_overwrite_var.
destruct (s x) as ((vx, px), cx) eqn:Hsx.
unfold fst. unfold snd.
assert (1 + (-1 + vx) = vx). { lia. }
rewrite H.
unfold update.
destruct (string_dec x y).
+ rewrite <- Hsx. rewrite e. reflexivity.
+ reflexivity.
Qed.

(* [inv (INC x)] è l'inverso di [INC x]. *)
Lemma INC_inv_INC_id: forall (s: store) (x y: ident),
  (eval (INC x;; inv (INC x)) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (INC_DEC_id s x y).
Qed.

(* [INC x] è l'inverso di [inv (INC x)]. *)
Lemma inv_INC_INC_id: forall (s: store) (x y: ident),
  (eval (inv (INC x);; INC x) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (DEC_INC_id s x y).
Qed.

(* [inv (DEC x)] è l'inverso di [DEC x]. *)
Lemma DEC_inv_DEC_id: forall (s: store) (x y: ident),
  (eval (DEC x;; inv (DEC x)) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (DEC_INC_id s x y).
Qed.

(* [DEC x] è l'inverso di [inv (DEC x)]. *)
Lemma inv_DEC_DEC_id: forall (s: store) (x y: ident),
  (eval (inv (DEC x);; DEC x) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (INC_DEC_id s x y).
Qed.

Lemma inv_INC_INC_id_evalI: forall (s: store) (x y: ident),
  (evalI (inv (INC x);; INC x) s) y = s y.
Proof. intros s x y.
rewrite (proj1 (evalI_to_eval_inv (inv (INC x);; INC x) s)).
unfold inv.
exact (DEC_INC_id s x y).
Qed.

Lemma INC_inv_INC_id_evalI: forall (s: store) (x y: ident),
  (evalI (INC x;; inv (INC x)) s) y = s y.
Proof. intros s x y.
rewrite (proj1 (evalI_to_eval_inv (INC x ;; inv (INC x)) s)).
unfold inv. exact (INC_DEC_id s x y).
Qed.

Lemma DEC_inv_DEC_id_evalI: forall (s: store) (x y: ident),
  (evalI (DEC x;; inv (DEC x)) s) y = s y.
Proof. intros s x y.
rewrite (proj1 (evalI_to_eval_inv (DEC x ;; inv (DEC x)) s)).
unfold inv. exact (DEC_INC_id s x y).
Qed.

Lemma inv_DEC_DEC_id_evalI: forall (s: store) (x y: ident),
  (evalI (inv (DEC x);; DEC x) s) y = s y.
Proof. intros s x y.
rewrite (proj1 (evalI_to_eval_inv (inv (DEC x) ;; DEC x) s)).
unfold inv. exact (INC_DEC_id s x y).
Qed.

Lemma POP_PUSH_id : forall (s: store) (x y: ident),
  (eval (POP x;; PUSH x) s) y = s y.
Proof.
intros s x y. 
unfold inv. unfold eval. 
rewrite update_same. rewrite push_inv_pop.
rewrite update_overwrite_var.
unfold update.
destruct (string_dec x y).
- rewrite <- e. reflexivity.
- reflexivity.
Qed.

Lemma PUSH_POP_id : forall (s: store) (x y: ident),
  (eval (PUSH x;; POP x) s) y = s y.
Proof.
intros s x y. 
unfold inv. unfold eval. 
rewrite update_same. rewrite pop_inv_push.
rewrite update_overwrite_var.
unfold update.
destruct (string_dec x y).
- rewrite <- e. reflexivity.
- reflexivity.
Qed.


(* [inv (POP x)] è l'inverso di [POP x]. *)
Lemma POP_inv_POP_id: forall (s: store) (x y: ident),
  (eval (POP x;; inv (POP x)) s) y = s y.
Proof. intros s x y. 
unfold inv.
exact (POP_PUSH_id s x y).
Qed.

(* [POP x] è l'inverso di [inv (POP x)]. *)
Lemma inv_POP_POP_id: forall (s: store) (x y: ident),
  (eval (inv (POP x);; POP x) s) y = s y.
Proof. intros s x y. 
unfold inv.
unfold inv.
exact (PUSH_POP_id s x y).
Qed.

(* [inv (PUSH x)] è l'inverso di [PUSH x]. *)
Lemma PUSH_inv_PUSH_id: forall (s: store) (x y: ident),
  (eval (PUSH x;; inv (PUSH x)) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (PUSH_POP_id s x y).
Qed.

(* [PUSH x] è l'inverso di [inv (PUSH x)] . *)
Lemma inv_PUSH_PUSH_id: forall (s: store) (x y: ident),
  (eval (inv (PUSH x);; PUSH x) s) y = s y.
Proof. intros s x y.
unfold inv.
exact (POP_PUSH_id s x y).
Qed.
