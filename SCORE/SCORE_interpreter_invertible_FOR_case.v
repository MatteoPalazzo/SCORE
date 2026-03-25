(* !!!!! TODO: GUARDARE IL TODO!!!!!!!!!!! *)

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
From CDF Require Import SCORE_wellformedness_properties.
From CDF Require Import SCORE_reversibility_general_properties.

(* From CDF Require Import SCORE_interpreter_PUSH_POP_defs.
From CDF Require Import SCORE_interpreter_PUSH_POP_properties. *)

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Open Scope SCORE_scope.

(* Print com_ind. *)


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

(* TODO: 
  - MODIFICARE IL LEMMA "iter_inverse_iter_function_id {A}" PER 
    LAVORARE SOLO SU RIGHT INVERSE E LEFT INVERSE
  - AGGIUNGERE PROPOSIZIONI SIMILI MA PER LEFT-INVERSE E RIGHT-INVERSE *)

Proposition reverse_is_left_inverse_gen : forall (f: com -> store -> store) (P: com),
  (forall s, f (inv P) (f P s) = s) ->
  left_inverse (fun s => f P s) (fun s => f (inv P) s). 
Proof. 
intros f P Hinv0.
unfold left_inverse.
assumption.
Qed.

Corollary reverse_is_left_inverse_eval : forall P,
  (forall s, eval (inv P) (eval P s) = s) ->
  left_inverse (fun s => eval P s) (fun s => eval (inv P) s) .
Proof. apply (reverse_is_left_inverse_gen eval).
Qed.

Corollary reverse_is_left_inverse_evalI : forall P,
  (forall s, evalI (inv P) (evalI P s) = s) ->
  left_inverse (fun s => evalI P s) (fun s => evalI (inv P) s) .
Proof. apply (reverse_is_left_inverse_gen evalI).
Qed.

Proposition reverse_is_right_inverse_gen : forall (f: com -> store -> store) (P: com),
  (forall s, f (P) (f (inv P) s) = s) ->
  right_inverse (fun s => f P s) (fun s => f (inv P) s). 
Proof. 
intros f P Hinv0.
unfold right_inverse.
assumption.
Qed.

Corollary reverse_is_right_inverse_eval : forall P,
  (forall s, eval P (eval (inv P) s) = s) ->
  right_inverse (fun s => eval P s) (fun s => eval (inv P) s) .
Proof. apply (reverse_is_right_inverse_gen eval).
Qed.

Corollary reverse_is_right_inverse_evalI : forall P,
  (forall s, evalI P (evalI (inv P) s) = s) ->
  right_inverse (fun s => evalI P s) (fun s => evalI (inv P) s) .
Proof. apply (reverse_is_right_inverse_gen evalI).
Qed.



Proposition reverse_is_invertible_gen : forall (f: com -> store -> store) (P: com),
  (forall s, f (inv P) (f P s) = s) ->
    (forall s, f P (f (inv P) s) = s) ->
  inverse (fun s => f P s) (fun s => f (inv P) s). 
Proof. 
intros f P Hinv0 Hinv1.
unfold inverse. 
split.
  + unfold left_inverse. assumption.
  + unfold right_inverse. assumption.
Qed.

(* Proposition invertible_imp_invertible : 
    (forall P s, eval (inv P) (eval P s) = s) ->
      (forall P s, eval P (eval (inv P) s) = s).
Proof.
intros.
assert (inv (inv P) = P) as HInvInvP. {
  exact (inv_self_dual P).
}
rewrite <- (HInvInvP) at 1.
auto.
Qed.

Proposition invertible_imp_invertible1 : forall P, 
    (forall s, eval (inv P) (eval P s) = s) ->
      (forall s, eval P (eval (inv P) s) = s).
Proof.
intros.
assert (forall P s, eval P (eval (inv P) s) = s). {
  apply invertible_imp_invertible.
  
assert (inv (inv P) = P) as HInvInvP. {
  exact (inv_self_dual P).
}
rewrite <- (HInvInvP) at 1.
auto.
Qed. *)


Corollary reverse_is_invertible_eval : forall P,
  (forall s, eval (inv P) (eval P s) = s) ->
    (forall s, eval P (eval (inv P) s) = s) ->
  inverse (fun s => eval P s) (fun s => eval (inv P) s) .
Proof. apply (reverse_is_invertible_gen eval).
Qed.

Corollary reverse_is_invertible_evalI : forall P,
  (forall s, evalI (inv P) (evalI P s) = s) ->
    (forall s, evalI P (evalI (inv P) s) = s) ->
  inverse (fun s => evalI P s) (fun s => evalI (inv P) s) .
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



(* Theorem eval_FOR_DEC_inv_FOR_INC_Luca: forall x y s,
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
Qed. *)


(* --------------------------- *)

(** Il caso induttivo finale completo.....  *)
(* Lemma FOR_inv_FOR_id:
forall (x:ident) (P:com),
(forall (s: store), 
   (eval (P;; inv P) s = s)) ->
(wfcom_rel P x) ->
(wfcom P) ->
(forall (s: store) (z : ident), 
  (eval ((FOR x P);; inv (FOR x P)) s z = s z)).
Proof.
intros x P IH HwfcomPx HwfcomP s z.
assert ({x = z} + {x <> z}) as HXAndZ. {
  exact (string_dec x z).
}
destruct HXAndZ as [Hxeqz | Hxneqz]. 
+ rewrite <- Hxeqz.
  repeat rewrite eval_unfold_SEQ.
  Search (inv (FOR ?x ?P) = (FOR ?x (inv ?P))).
  rewrite inv_unfold_FOR.
  - assert ((eval (FOR x P) s) x = s x).
    { apply FOR_lead_var_invariant;  assumption. }
    assert (eval (FOR x (inv P)) (eval (FOR x P) s) x = (eval (FOR x P) s) x).
    { apply FOR_lead_var_invariant. 
      rewrite wfcom_inv in HwfcomP. assumption.
      apply wfcom_rel_inv in HwfcomPx.
      assumption. }
    rewrite H0. rewrite H.
    reflexivity.
(*  - assert ((eval (FOR x (inv P)) s) x = s x).
    { apply FOR_lead_var_invariant. 
      rewrite wfcom_inv in HwfcomP. assumption.
      rewrite wfcom_rel_inv in HwfcomPx. assumption. }
    assert (eval (FOR x P) (eval (FOR x (inv P)) s) x = (eval (FOR x (inv P)) s) x).
    { apply FOR_lead_var_invariant. 
      assumption. assumption. }
    rewrite H0. rewrite H.
    reflexivity. *)
+ repeat rewrite eval_unfold_SEQ.
  repeat rewrite inv_unfold_FOR.
  destruct (s x) as ((vx0, lx0), ex0) eqn:Hsx.
  destruct vx0 eqn:Hvx0. 
  - assert (eval (FOR x P) s = s). 
    { apply (FOR_to_Ziter_Eq s x P 0 lx0 ex0). 
      - assumption.
      - reflexivity. }
    assert (eval (FOR x (inv P)) s = s). 
    { apply (FOR_to_Ziter_Eq s x (inv P) 0 lx0 ex0). 
      - assumption.
      - reflexivity. }
    repeat rewrite H.
    repeat rewrite H0. 
    reflexivity.
    (* rewrite H. 
    tauto. *)
  - (* split. *)
    (* * *) Check eval_unfold_FOR_Gt. 
      set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        unfold s'. 
        Check FOR_lead_var_invariant. 
        apply FOR_lead_var_invariant. 
        assumption. assumption. 
      }
      rewrite Hsx in s'xEqsx.
      rewrite (eval_unfold_FOR_Gt s' x (Z.pos p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => eval (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0).
      set (f := fun s'0 : store => eval P s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (Z.pos p))) (Z.to_pos (Z.pos p)) 
        = s). {
        apply iter_left_inverse_iter_function_id. 
        apply reverse_is_left_inverse_eval.
        intro. rewrite <- eval_unfold_SEQ.
        exact (IH s0).
      }
      rewrite H. reflexivity.
      assumption.
      exact (Zgt_pos_0 p).
      assumption.
      exact (Zgt_pos_0 p).
  (* * admit. *)
  -   set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        unfold s'. 
        Check FOR_lead_var_invariant. 
        apply FOR_lead_var_invariant. 
        assumption. assumption. 
      }
      rewrite Hsx in s'xEqsx.
      rewrite (eval_unfold_FOR_Lt s' x (Z.neg p) (lx0) (ex0)).
      2: assumption.
      2: apply Zlt_neg_0.
      assert ((forall s, eval(P ;; inv(P)) s = s)
        -> (forall s, evalI(P ;; inv(P)) s = s)). {
        intros.
        assert (inv (inv P) = P) as HInvInvP. {
          exact (inv_self_dual P).
        }
        Search "evalI_to".
        Check evalI_to_eval_inv.
        rewrite (proj1 (evalI_to_eval_inv (P;; inv P) s0)).
        Search (inv _ = _).
        rewrite inv_unfold_SEQ.
        rewrite inv_self_dual.
        auto.
      }
      assert (forall s : store, evalI (P;; inv P) s = s). {
        exact (H IH).
      }
      set (f := fun s'0 : store => evalI (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0).
      set (f_inv := fun s'0 : store => evalI P s'0).
      assert (Pos.iter f (Pos.iter f_inv s (Z.to_pos (- Z.neg p))) (Z.to_pos (- Z.neg p)) = s). {
        apply iter_left_inverse_iter_function_id. 
        apply reverse_is_left_inverse_evalI.
        intro. rewrite <- evalI_unfold_SEQ.
        Check evalI_to_eval_inv.
        rewrite (proj1 (evalI_to_eval_inv (inv P ;; P) s0)).
        rewrite inv_unfold_SEQ.
        rewirte 
        exact (H0 s0).
      }
      (* assert (evalI (inv P) = eval P). {
        apply functional_extensionality.
        intro.
        rewrite (proj2 (evalI_to_eval_inv P x0)).
        reflexivity.      
      } *)
      rewrite H.
      set (f := fun s'0 : store => eval (P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0).
       assert (evalI (P) = eval (inv P)). {
        apply functional_extensionality.
        intro.
        rewrite (proj1 (evalI_to_eval_inv P x0)).
        reflexivity.      
      }
      rewrite H0.
      set (f_inv := fun s'0 : store => eval (inv P) s'0).
      assert (Pos.iter f (Pos.iter f_inv s (Z.to_pos (- Z.neg p))) (Z.to_pos (- Z.neg p)) 
        = s). {
        apply iter_right_inverse_iter_function_id.
        unfold right_inverse.
        unfold f. unfold f_inv.
        
        apply reverse_is_right_inverse_eval.
        assert (forall s : store, evalI (P;; inv P) s = s) as IHL. {
          intro.
          Check evalI_to_eval_inv.
          rewrite (proj1 (evalI_to_eval_inv (P;; inv P) s0)).
          rewrite inv_unfold_SEQ.
          rewrite inv_self_dual.
          Search (inv _ = _).
          exact (proj1 (IH s0)).        
        }
        assert (forall s : store, evalI (inv P;;  P) s = s) as IHR. {
          intro.
          Check evalI_to_eval_inv.
          rewrite (proj1 (evalI_to_eval_inv (inv P;; P) s0)).
          rewrite inv_unfold_SEQ.
          rewrite inv_self_dual.
          exact (proj2 (IH s0)).        
        }
        assert (inverse f f_inv) as fInvf_inv. {
          apply reverse_is_invertible_evalI.
          + intro s0.
            rewrite <- evalI_unfold_SEQ. 
            exact (IHR s0).
          + intro s0. rewrite <- evalI_unfold_SEQ. exact (IHL s0).
        }
        assert (inverse f_inv f) as f_invInvf. {
          apply reverse_is_invertible_evalI.
          + intro s0.
            rewrite <- evalI_unfold_SEQ. 
            exact (IHR s0).
          + intro s0. rewrite <- evalI_unfold_SEQ. exact (IHL s0).
        }
        apply iter_inverse_iter_function_id. 
        exact fInvf_inv.
        exact f_invInvf.
      }
      rewrite H. reflexivity.
      assumption.
      exact (Zlt_neg_0 p).
Qed. *)


(* Lemma FOR_lead_var_invariant:
forall (x : ident) (P : com),
  (wfcom P) ->
  (wfcom_rel P x) -> 
(forall s, eval (FOR x P) s x = s x).
Proof.
intros.
assert (wfcom (FOR x P)) as wfcomFOR.
{ simpl. 
  split.
  + assumption.
  + apply (wfcom_rel_excludes_wr P x) in H0. assumption. 
}
rewrite non_wrvars_preserved_eval.
reflexivity.
simpl in wfcomFOR.
destruct wfcomFOR.
simpl.
assumption.
Qed. *)

Lemma FOR_lead_var_invariant:
forall (x : ident) (P : com),
  (wfcom (FOR x P)) ->
(forall s, eval (FOR x P) s x = s x).
Proof.
intros.
rewrite non_wrvars_preserved_eval.
+ reflexivity.
+ simpl in H.
  unfold vars_wr. fold vars_wr.
  tauto.
Qed.

Lemma FOR_inv_FOR_id:
forall P : com,
(wfcom P ->
 forall (s : store) (z : ident), eval (P;; inv P) s z = s z /\ eval (inv P;; P) s z = s z) ->
forall x : ident,
wfcom (FOR x P) ->
forall (s : store) (z : ident),
eval (FOR x P;; inv (FOR x P)) s z = s z /\ eval (inv (FOR x P);; FOR x P) s z = s z.
Proof.
intros P IH x HwfcomForXP s z.
assert (wfcom P ->
     forall (s : store) (z : ident), eval (P;; inv P) s z = s z) as IHL. {
  intros.
  exact (proj1 (IH H s0 z0)).
}
assert (wfcom P ->
     forall (s : store) (z : ident), eval (inv P;; P) s z = s z) as IHR. {
  intros.
  exact (proj2 (IH H s0 z0)).
}
assert (In P (sub_com (FOR x P))) as HInPFORXP. {
  simpl.
  tauto.
}
assert (wfcom P) as HwfcomP. {
  apply (wfcom_downc_weaker (FOR x P) P) in HwfcomForXP; 
    assumption.
} 
assert (wfcom (FOR x (inv P))) as HwfcomFORXInvP. {
  rewrite wfcom_inv in HwfcomForXP.
  rewrite inv_unfold_FOR in HwfcomForXP.
  assumption.
}
(* assert (wfcom_rel P x) as HwfcomRelPX. {
  unfold wfcom in HwfcomForXP. fold wfcom in HwfcomForXP.
  unfold wfcom_rel. fold wfcom_rel.
  apply (wfcom_downc_weaker (FOR x P) P) in HwfcomForXP; 
    assumption.
} *)
assert ({x = z} + {x <> z}) as HXOrZ. {
  exact (string_dec x z).
}
destruct HXOrZ as [Hxeqz | Hxneqz]. 
+ rewrite <- Hxeqz.
  repeat rewrite eval_unfold_SEQ.
  rewrite inv_unfold_FOR.
  repeat rewrite (FOR_lead_var_invariant); tauto. 
(*  - assert ((eval (FOR x (inv P)) s) x = s x).
    { apply FOR_lead_var_invariant. 
      rewrite wfcom_inv in HwfcomP. assumption.
      rewrite wfcom_rel_inv in HwfcomPx. assumption. }
    assert (eval (FOR x P) (eval (FOR x (inv P)) s) x = (eval (FOR x (inv P)) s) x).
    { apply FOR_lead_var_invariant. 
      assumption. assumption. }
    rewrite H0. rewrite H.
    reflexivity. *)
+ repeat rewrite eval_unfold_SEQ.
  repeat rewrite inv_unfold_FOR.
  destruct (s x) as ((vx0, lx0), ex0) eqn:Hsx.
  destruct vx0 eqn:Hvx0. 
  - assert (eval (FOR x P) s = s). 
    { apply (FOR_to_Ziter_Eq s x P 0 lx0 ex0); tauto. } 
    assert (eval (FOR x (inv P)) s = s). 
    { apply (FOR_to_Ziter_Eq s x (inv P) 0 lx0 ex0); tauto. }
    rewrite H. rewrite H0. rewrite H. 
    tauto.
  - split.
    * set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        apply FOR_lead_var_invariant. assumption.
      }
      rewrite (eval_unfold_FOR_Gt s' x (Z.pos p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => eval (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0).
      set (f := fun s'0 : store => eval P s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (Z.pos p))) (Z.to_pos (Z.pos p)) 
      = s). {
        apply iter_left_inverse_iter_function_id.
        apply reverse_is_left_inverse_eval.
        intro.
        rewrite eval_fold_SEQ.
        apply functional_extensionality.
        exact (IHL HwfcomP s0).
      }
      rewrite H. reflexivity.
      all: rewrite Hsx in s'xEqsx.
      1, 3: assumption.
      all: apply Zgt_pos_0.
    * set (s' := eval (FOR x (inv P)) s).
      assert (s' x = s x) as s'xEqsx. { 
        apply FOR_lead_var_invariant. assumption.
      }
      rewrite (eval_unfold_FOR_Gt s' x (Z.pos p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => eval P s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0).
      set (f := fun s'0 : store => eval (inv P) s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (Z.pos p))) (Z.to_pos (Z.pos p)) 
      = s). {
        apply iter_right_inverse_iter_function_id.
        apply reverse_is_right_inverse_eval.
        intro.
        rewrite eval_fold_SEQ.
        apply functional_extensionality.
        exact (IHR HwfcomP s0).
      }
      rewrite H. reflexivity.
      all: rewrite Hsx in s'xEqsx.
      1, 3: assumption.
      all: apply Zgt_pos_0.
  (* * admit. *)
  - split.
    * set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        apply FOR_lead_var_invariant. assumption.
      }
      rewrite (eval_unfold_FOR_Lt s' x (Z.neg p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => evalI (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0).
      set (f := fun s'0 : store => evalI P s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (- Z.neg p))) (Z.to_pos (- Z.neg p)) 
      = s). {
        apply iter_left_inverse_iter_function_id.
        apply reverse_is_left_inverse_evalI.
        intro.
        rewrite evalI_fold_SEQ.
        rewrite (proj1 (evalI_to_eval_inv (inv P ;; P) s0)).
        rewrite inv_unfold_SEQ.
        rewrite inv_self_dual.
        apply functional_extensionality.
        exact (IHR HwfcomP s0).
      }
      rewrite H. reflexivity.
      all: rewrite Hsx in s'xEqsx.
      1, 3: assumption.
      all: apply Zlt_neg_0.
    * set (s' := eval (FOR x (inv P)) s).
      assert (s' x = s x) as s'xEqsx. { 
        apply FOR_lead_var_invariant. assumption.
      }
      rewrite (eval_unfold_FOR_Lt s' x (Z.neg p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => evalI P s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0).
      set (f := fun s'0 : store => evalI (inv P) s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (- Z.neg p))) (Z.to_pos (- Z.neg p)) 
      = s). {
        apply iter_right_inverse_iter_function_id.
        apply reverse_is_right_inverse_evalI.
        intro.
        rewrite evalI_fold_SEQ.
        rewrite (proj1 (evalI_to_eval_inv (P;; inv P) s0)).
        rewrite inv_unfold_SEQ.
        rewrite inv_self_dual.
        apply functional_extensionality.
        exact (IHL HwfcomP s0).
      }
      rewrite H. reflexivity.
      all: rewrite Hsx in s'xEqsx.
      1, 3: assumption.
      all: apply Zlt_neg_0.
Qed.


(** Il caso induttivo finale completo.....  *)
(* Lemma FOR_inv_FOR_id_redundant:
forall (x:ident) (P:com),
(forall (s: store), 
   (eval (P;; inv P) s = s) 
   /\ (eval (inv P;; P) s = s)) ->
(wfcom_rel P x) ->
(wfcom P) ->
(forall (s: store) (z : ident), (eval ((FOR x P);; inv (FOR x P)) s z = s z)) /\ 
(forall (s: store) (z: ident), (eval (inv (FOR x P);; (FOR x P)) s z = s z)).
Proof.
intros x P.
assert ({x = z} + {x <> z}) as HXAndZ. {
  exact (string_dec x z).
}
destruct HXAndZ as [Hxeqz | Hxneqz]. 
+ rewrite <- Hxeqz.
  repeat rewrite eval_unfold_SEQ.
  Search (inv (FOR ?x ?P) = (FOR ?x (inv ?P))).
  rewrite inv_unfold_FOR.
  - assert ((eval (FOR x P) s) x = s x).
    { apply FOR_lead_var_invariant;  assumption. }
    assert (eval (FOR x (inv P)) (eval (FOR x P) s) x = (eval (FOR x P) s) x).
    { apply FOR_lead_var_invariant. 
      rewrite wfcom_inv in HwfcomP. assumption.
      apply wfcom_rel_inv in HwfcomPx.
      assumption. }
    rewrite H0. rewrite H.
    reflexivity.
(*  - assert ((eval (FOR x (inv P)) s) x = s x).
    { apply FOR_lead_var_invariant. 
      rewrite wfcom_inv in HwfcomP. assumption.
      rewrite wfcom_rel_inv in HwfcomPx. assumption. }
    assert (eval (FOR x P) (eval (FOR x (inv P)) s) x = (eval (FOR x (inv P)) s) x).
    { apply FOR_lead_var_invariant. 
      assumption. assumption. }
    rewrite H0. rewrite H.
    reflexivity. *)
+ repeat rewrite eval_unfold_SEQ.
  repeat rewrite inv_unfold_FOR.
  destruct (s x) as ((vx0, lx0), ex0) eqn:Hsx.
  destruct vx0 eqn:Hvx0. 
  - assert (eval (FOR x P) s = s). 
    { apply (FOR_to_Ziter_Eq s x P 0 lx0 ex0). 
      - assumption.
      - reflexivity. }
    assert (eval (FOR x (inv P)) s = s). 
    { apply (FOR_to_Ziter_Eq s x (inv P) 0 lx0 ex0). 
      - assumption.
      - reflexivity. }
    repeat rewrite H.
    repeat rewrite H0. 
    reflexivity.
    (* rewrite H. 
    tauto. *)
  - (* split. *)
    (* * *) Check eval_unfold_FOR_Gt. 
      set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        unfold s'. 
        Check FOR_lead_var_invariant. 
        apply FOR_lead_var_invariant. 
        assumption. assumption. 
      }
      rewrite Hsx in s'xEqsx.
      rewrite (eval_unfold_FOR_Gt s' x (Z.pos p) (lx0) (ex0)).
      set (f_inv := fun s'0 : store => eval (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0).
      set (f := fun s'0 : store => eval P s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (Z.pos p))) (Z.to_pos (Z.pos p)) 
        = s). {
        assert (forall s : store, eval (P;; inv P) s = s) as IHL. {
          intro. exact (proj1 (IH s0)).        
        }
        assert (forall s : store, eval (inv P;; P) s = s) as IHR. {
          intro. exact (proj2 (IH s0)).        
        }
        assert (inverse f f_inv) as fInvf_inv. {
          apply reverse_is_invertible_eval.
          + intro s0.
            rewrite <- eval_unfold_SEQ. 
            exact (IHL s0).
          + intro s0. rewrite <- eval_unfold_SEQ. exact (IHR s0).
        }
        (* assert (inverse f_inv f) as f_invInvf. {
          apply reverse_is_invertible_eval.
          + intro s0.
            rewrite <- eval_unfold_SEQ. 
            exact (IHL s0).
          + intro s0. rewrite <- eval_unfold_SEQ. exact (IHR s0).
        } *)
        apply iter_inverse_iter_function_id. 
        exact fInvf_inv.
      }
      rewrite H. reflexivity.
      assumption.
      exact (Zgt_pos_0 p).
      assumption.
      exact (Zgt_pos_0 p).
  (* * admit. *)
  - Check eval_unfold_FOR_Gt. 
      set (s' := eval (FOR x P) s).
      assert (s' x = s x) as s'xEqsx. { 
        unfold s'. 
        Check FOR_lead_var_invariant. 
        apply FOR_lead_var_invariant. 
        assumption. assumption. 
      }
      rewrite Hsx in s'xEqsx.
      rewrite (eval_unfold_FOR_Lt s' x (Z.neg p) (lx0) (ex0)).
      2: assumption.
      2: apply Zlt_neg_0.
      set (f_inv := fun s'0 : store => evalI (inv P) s'0).
      unfold s'.
      rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx0 ex0).
      set (f := fun s'0 : store => evalI P s'0).
      assert (Pos.iter f_inv (Pos.iter f s (Z.to_pos (- Z.neg p))) (Z.to_pos (- Z.neg p)) 
        = s). {
        assert (forall s : store, evalI (P;; inv P) s = s) as IHL. {
          intro.
          Check evalI_to_eval_inv.
          rewrite (proj1 (evalI_to_eval_inv (P;; inv P) s0)).
          rewrite inv_unfold_SEQ.
          rewrite inv_self_dual.
          Search (inv _ = _).
          exact (proj1 (IH s0)).        
        }
        assert (forall s : store, evalI (inv P;;  P) s = s) as IHR. {
          intro.
          Check evalI_to_eval_inv.
          rewrite (proj1 (evalI_to_eval_inv (inv P;; P) s0)).
          rewrite inv_unfold_SEQ.
          rewrite inv_self_dual.
          exact (proj2 (IH s0)).        
        }
        assert (inverse f f_inv) as fInvf_inv. {
          apply reverse_is_invertible_evalI.
          + intro s0.
            rewrite <- evalI_unfold_SEQ. 
            exact (IHR s0).
          + intro s0. rewrite <- evalI_unfold_SEQ. exact (IHL s0).
        }
        assert (inverse f_inv f) as f_invInvf. {
          apply inverse_f_g_iff_inverse_g_f.
          assumption.
        }
        apply iter_inverse_iter_function_id.
        assumption.
      }
      rewrite H. reflexivity.
      assumption.
      exact (Zlt_neg_0 p).
Qed. *)

(*+

        unfold f.
        unfold f_inv.
        Check reverse_is_invertible_eval.
        
      }
      apply iter_inverse_iter_function_id. 
      rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx0 ex0 Hsx).
      set (f := fun s' : store => eval P s').
      (* unfold f. *)
      set (s' := (Pos.iter f s (Z.to_pos (Z.pos p)))).
      
  
    
    
  *  
  assert (s x = 0 \/ s x > 0 \/ s x < 0).  
  * rewrite eval_unfold_SEQ.
    
  
 
+ admit.
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
Qed.*)