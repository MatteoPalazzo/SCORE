From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.

(* From Coq Require Import FunctionalExtensionality. *)
From CDF Require Import CommonDefinitions.
Module CD := CommonDefinitions.

(* From CDF Require Import Sequences. *)

From CDF Require Import SCORE_interpreter . 
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter_invertible_SEQ_case.
From CDF Require Import SCORE_interpreter_invertible_base_cases.

(* From CDF Require Import SCORE_interpreter_PUSH_POP_defs.
From CDF Require Import SCORE_interpreter_PUSH_POP_properties. *)

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Open Scope SCORE_scope.

(* Print com_ind. *)

Check Z_dec.

(* LUCA: penso proprio siano da cancellare

Lemma Ziter_pred_Lt_left: forall v f (s: store),
  v < 0 -> Z.iter (-v) f s = f (Z.iter (-(v+1)) f s).
Admitted.

Lemma Ziter_pred_Lt_right: forall v f (s: store),
  v < 0 -> Z.iter (-v) f s = Z.iter (-(v+1)) f (f s).
Admitted.

Lemma eval_FOR_SKIP_id_one_step: forall x s,
eval (FOR x SKIP) s = s.
(* eval (FOR x SKIP) s x = s x. *)
Admitted. 
*)


(* LUCA: aggiunti, ma inutili?
Rimarcano l'idea che se [x <> y] allora x non è scritto da
[INC y] o [DEC y] e che se x non è nella variabili scritte 
da [INC x] o [DEC x] allora il valore di [x] memorizzato in
un qualche [s]tore, non cambia
*)
Lemma xNEQy_impl_xNotIn_DECy: forall x y, 
  x <> y -> ~ (In x (vars_wr (DEC y))).
Proof. simpl. unfold "<>". intros.
apply H. destruct H0.
- rewrite H0. reflexivity.
- contradiction.
Qed.

Lemma xNEQy_impl_xNotIn_INCy: forall x y, 
  x <> y -> ~ (In x (vars_wr (INC y))).
Proof. simpl. unfold "<>". intros.
apply H. destruct H0.
- rewrite H0. reflexivity.
- contradiction.
Qed.

Lemma eval_DEC_wf: forall s x y, 
  ~ (In x (vars_wr (DEC y))) ->
      (eval (DEC y) s) x = s x.
Proof. intros.
Check (proj1 (non_wrvars_preserved (DEC y) x H s)).
rewrite (proj1 (non_wrvars_preserved (DEC y) x H s)).
reflexivity. 
Qed.

Lemma eval_INC_wf: forall s x y, 
  ~ (In x (vars_wr (INC y))) ->
      (eval (INC y) s) x = s x.
Proof. intros.
(* Check (proj1 (non_wrvars_preserved (INC y) x H s)). *)
rewrite (proj1 (non_wrvars_preserved (INC y) x H s)).
reflexivity. 
Qed.


(* LUCA: è probabile che ci servano versioni in cui usiamo

[eval P (evalI P s) = s] e [evalI P (eval P s) = s].

Questo suggerisce che sarebbe bello avere eval e evalI definite
indipoendentemente l'una dall'altra seguendo l'idea i 
Zneg = Z.neg positive

*)
Proposition reverse_is_invertible_gen : forall (f: com -> store -> store) (P: com),
  (forall s, f (inv P) (f P s) = s) ->
    (forall s, f P (f (inv P) s) = s) ->
  inverse (fun s => f P s) (fun s => f (inv P) s) 
    /\   inverse (fun s => f (inv P) s)  (fun s => f P s) .
Proof. 
intros f P Hinv0 Hinv1.
unfold inverse. split.
- split. 
  + unfold left_inverse. assumption.
  + unfold left_inverse. assumption.
- split. 
  + unfold right_inverse. assumption.
  + unfold right_inverse. assumption.
Qed.

Corollary reverse_is_invertible_eval : forall P,
  (forall s, eval (inv P) (eval P s) = s) ->
    (forall s, eval P (eval (inv P) s) = s) ->
  inverse (fun s => eval P s) (fun s => eval (inv P) s) 
    /\   inverse (fun s => eval (inv P) s)  (fun s => eval P s) .
Proof. apply (reverse_is_invertible_gen eval).
Qed.

Corollary reverse_is_invertible_evalI : forall P,
  (forall s, evalI (inv P) (evalI P s) = s) ->
    (forall s, evalI P (evalI (inv P) s) = s) ->
  inverse (fun s => evalI P s) (fun s => evalI (inv P) s) 
    /\   inverse (fun s => evalI (inv P) s)  (fun s => evalI P s) .
Proof. apply (reverse_is_invertible_gen evalI).
Qed.


(* ORIGINALE DI MATTEO 
Lemma reverse_is_invertible : forall P,
  (forall s, eval (inv P) (eval P s) = s) ->
    (forall s, eval P (eval (inv P) s) = s) ->
  inverse (fun s => eval P s) (fun s => eval (inv P) s) 
    /\   inverse (fun s => eval (inv P) s)  (fun s => eval P s) .
Proof. 
intros P Hinv0 Hinv1.
unfold inverse. split.
- split. 
  + unfold left_inverse. assumption.
  + unfold left_inverse. assumption.
- split. 
  + unfold right_inverse. assumption.
  + unfold right_inverse. assumption.
Qed. *)


Lemma zNEQxy_impl_zNotIn_FORINCDECy: forall x y z,
  z <> x -> z <> y ->
    ~ (In z (vars_wr ((FOR x (INC y)) ;; (FOR x (DEC y))))).
Proof. simpl. unfold "<>". intros.
destruct H1.
- apply H0. rewrite H1. reflexivity.
- destruct H1.
  + apply H0. rewrite H1. reflexivity.
  + assumption.
Qed.

(** Identifies three cases, depending on the value of [z] and
on the writable variable names in [FOR ...]
*)
Lemma zNEQxy_impl_zNotIn_FORINCDECy_dec: forall x y z,
  {z = x} + {z = y} + ~(In z (vars_wr ((FOR x (INC y)) ;; (FOR x (DEC y))))).
Proof. intros.
destruct (string_dec z x).
- left. left. subst. reflexivity.  
- destruct (string_dec z y). 
  + left. right. subst. reflexivity.
  + right.
    (* Check (zNEQxy_impl_zNotIn_FORINCDECy x y z n n0). *)
    apply (zNEQxy_impl_zNotIn_FORINCDECy x y z n n0).
Qed.



Theorem eval_FOR_DEC_inv_FOR_INC_Luca: forall x y s,
  x <> y ->
   (forall z, eval ((FOR x (INC y)) ;; (FOR x (DEC y))) s z = s z).
Proof.
intros x y s xneqy z.
(* Il valore di z distingue tre casi *)
destruct (zNEQxy_impl_zNotIn_FORINCDECy_dec x y z) as [[zeqx | zeqy] | znotin].
+ (* zexq: z = x *)
  apply non_wrvars_preserved. (* SCORE_interpreter.v *)
  rewrite zeqx. simpl.
  intro H. destruct H.
  * subst. contradiction.
  * destruct H.
    - subst. contradiction.
    - assumption.
+ (* zeqx: z = y *)
  (* Search eval.  *)
  rewrite eval_unfold_SEQ. (* SCORE_interpreter.v *)
  (* x mantine valore dopo il primo FOR *)
  assert (eval (FOR x (INC y)) s x = s x) as Hxpresv. {
    apply non_wrvars_preserved. intro H. 
     destruct H. 
    + subst. contradiction.
    + simpl in H. assumption. 
  }
  destruct (s x) as ((vx0, lx0), ex0) eqn:Hsx.
  destruct vx0 eqn:Hvx0.
  * (* Hvx0: vx0 = 0 *) 
    assert (HeqEvalDx: eval (FOR x (INC y)) s = s). {
      apply (eval_unfold_FOR_Eq s x 0 lx0 ex0 Hsx). (* SCORE_interpreter.v *)
      reflexivity.
    }
    rewrite HeqEvalDx.
    assert (HeqEvalSx: eval (FOR x (DEC y)) s = s). {
      apply (eval_unfold_FOR_Eq s x  0 lx0 ex0 Hsx). (* SCORE_interpreter.v *)
      reflexivity.
    }
    rewrite HeqEvalSx.
    reflexivity.
  * (* Hvx0: vx0 = Z.pos p *)
    assert (HposGt0: Z.pos p >  0). { lia. }
    assert (HevalToPosL: eval (FOR x (DEC y)) (eval (FOR x (INC y)) s) = 
                Pos.iter (fun s' => eval (DEC y) s') (eval (FOR x (INC y)) s) p ). { 
      (* Check (eval_unfold_FOR_Gt (eval (FOR x (INC y)) s) x (Z.pos p) lx0 ex0 Hxpresv HposGt0 (DEC y)). *)
      apply (eval_unfold_FOR_Gt (eval (FOR x (INC y)) s) x (Z.pos p) lx0 ex0 Hxpresv HposGt0 (DEC y)). (* SCORE_interpreter.v *)
    }
    rewrite HevalToPosL.
    assert (HevalToPosR: eval (FOR x (INC y)) s = Pos.iter (fun s' => eval (INC y) s') s p) . { 
      (* Check (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0 Hsx HposGt0 (INC y)). *)
      apply (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0 Hsx HposGt0 (INC y)). (* SCORE_interpreter.v *)
    }
    rewrite HevalToPosR.
    (* dimostra che DEC y e INC y sono uno l'inversa dell'altra secondo le definizioni
      date in CommonDefinitions*)
    assert (Hinv1: inverse (fun s' => eval (DEC y) s') (fun s' => eval (INC y) s')). {
      apply reverse_is_invertible_eval. (* this file *)
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite eval_fold_SEQ. (* SCORE_interpreter.v *)
        apply (INC_inv_INC_id s0 y x0). (* SCORE_interpreter_invertible_base_cases *)
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite eval_fold_SEQ. (* SCORE_interpreter.v *)
        apply (inv_INC_INC_id s0 y x0). (* SCORE_interpreter_invertible_base_cases*)
    }
    assert (Hinv2: inverse (fun s' => eval (INC y) s') (fun s' => eval (DEC y) s')). {
      apply reverse_is_invertible_eval. (* this file *)
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite eval_fold_SEQ. (* SCORE_interpreter.v *)
        apply (DEC_inv_DEC_id s0 y x0). (* SCORE_interpreter_invertible_base_cases*)
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite eval_fold_SEQ. (* SCORE_interpreter.v *)
        apply (inv_DEC_DEC_id s0 y x0). (* SCORE_interpreter_invertible_base_cases*)
    }
    (* clear zeqy. *)
    (* revert z. *)
    rewrite (
      iter_inverse_iter_function_id 
        (fun s' : store => eval (INC y) s')
        (fun s' : store => eval (DEC y) s') 
        Hinv2 Hinv1 p s).
    (* intro z. *)
    reflexivity.
  * (* Hvx0: vx0 = Z.neg p *)
    assert (HnegLt0: Z.neg p < 0). { lia. }
    assert (HevalToIterL: eval (FOR x (DEC y)) (eval (FOR x (INC y)) s) = 
              Pos.iter (fun s' => evalI (DEC y) s') (eval (FOR x (INC y)) s) (Z.to_pos (- Z.neg p)) ). { 
      (* Check (eval_unfold_FOR_Lt (eval (FOR x (INC y)) s) x (Z.neg p) lx0 ex0 Hxpresv HnegLt0 (DEC y)).       *)
      apply (eval_unfold_FOR_Lt (eval (FOR x (INC y)) s) x (Z.neg p) lx0 ex0 Hxpresv HnegLt0 (DEC y)).
    }
    rewrite HevalToIterL.
    (* apro l'eval più interna *)
    assert (HevalToIterR: eval (FOR x (INC y)) s = 
              Pos.iter (fun s' => evalI (INC y) s') s (Z.to_pos (- Z.neg p))). { 
      (* Check (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0 Hsx HnegLt0 (INC y)). *)
      apply (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0 Hsx HnegLt0 (INC y)).
    }
    rewrite HevalToIterR.
    assert (Hinv1: inverse (fun s' => evalI (DEC y) s') (fun s' => evalI (INC y) s')). {
      apply reverse_is_invertible_evalI.
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite evalI_fold_SEQ.
        apply (inv_INC_INC_id_evalI s0 y x0).
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite evalI_fold_SEQ.
        apply (INC_inv_INC_id_evalI s0 y x0).
    }
    assert (Hinv2: inverse (fun s' => evalI (INC y) s') (fun s' => evalI (DEC y) s')). {
      apply reverse_is_invertible_evalI.
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite evalI_fold_SEQ.
        apply (inv_DEC_DEC_id_evalI s0 y x0).
      + intro s0.
        apply functional_extensionality.
        intro x0.
        rewrite evalI_fold_SEQ.
        apply (DEC_inv_DEC_id_evalI s0 y x0).    
    }
    rewrite (
      iter_inverse_iter_function_id 
        (fun s' : store => evalI (INC y) s')
        (fun s' : store => evalI (DEC y) s') Hinv2 Hinv1 (Z.to_pos (- Z.neg p)) s
        ).
    reflexivity.
+ (* z not among the variables of  *) 
  apply non_wrvars_preserved.
  assumption.
Qed.

(** Il caso induttivo finale completo.....  *)
Lemma FOR_inv_FOR_id:
forall (x:ident) (P:com),
(forall (s: store), 
   (eval (P;; inv P) s = s) 
   /\ (eval (inv P;; P) s = s)) ->
(forall (s: store), 
  (eval ((FOR x P);; inv (FOR x P)) s = s)
  /\ (eval (inv (FOR x P);; (FOR x P)) s = s)).
Admitted.