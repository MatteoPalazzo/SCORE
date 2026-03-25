From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
Import ListNotations.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import CommonDefinitions.
From CDF Require Import Sequences.
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter.
From CDF Require Import SCORE_invertible_base.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Check Z.iter.
Check hd_error.
Print option.

Open Scope SCORE_scope.

(* **************** *)
(* L'idea è che [eval] applicato a [P;;Q] distribuisce, prima valutando [P] e poi [Q]. 

Il princpio induttivo applicato a [com] suggerisce di dimostrare la distibuzione di [eval] un passo alla volta, cioè istanziando [P], per poi dimostare al distribuzione per un qualsiasi [Q].
*)
Definition SEQ_inv_SEQ_id (P: com) : Prop := forall (s: store),
(forall x, exists h t, s x = h::t) 
  -> forall (y: ident),  eval (P;; inv P) s y = s y.

(* Rendiamo espliciti tutti i lemmi necessari a dimostrare:
> forall (P:com), evalSEQdistrL P.
*)
Check com_ind.
Check (com_ind SEQ_inv_SEQ_id).

Lemma SEQ_inv_SEQ_id_SKIP:
    SEQ_inv_SEQ_id SKIP.
Proof. unfold SEQ_inv_SEQ_id. simpl. reflexivity.
Qed.

Lemma SEQ_inv_SEQ_id_PUSH : forall x, 
SEQ_inv_SEQ_id (PUSH x).
Proof. unfold SEQ_inv_SEQ_id. 
intros. apply PUSH_inv_PUSH_id.
Qed.

Lemma SEQ_inv_SEQ_id_POP : forall x, 
SEQ_inv_SEQ_id (POP x).
Proof. unfold SEQ_inv_SEQ_id. 
simpl. intros.
exists (update x (tl (s x)) s).
split.
+ reflexivity.
+ assumption.
Qed.

Lemma SEQ_inv_SEQ_id_DEC : forall x, 
SEQ_inv_SEQ_id (DEC x).
Admitted.

Lemma SEQ_inv_SEQ_id_INC : forall x, 
SEQ_inv_SEQ_id (INC x).
Admitted.

Lemma SEQ_inv_SEQ_id_SEQ : forall P' : com, 
SEQ_inv_SEQ_id P' -> 
     forall Q' : com, evalSEQdistrL Q' -> evalSEQdistrL (P';; Q').
Admitted.

Lemma SEQ_inv_SEQ_id_FOR : forall (x : ident) (P' : com), 
SEQ_inv_SEQ_id P' -> evalSEQdistrL (FOR x P').
Admitted.

Proposition SEQ_inv_SEQ_id_prop : forall (P : com), 
SEQ_inv_SEQ_id P.
Admitted.
