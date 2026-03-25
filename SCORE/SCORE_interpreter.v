From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.

(* Search Z.iter.
Search nat_rect.
Search fold_right. *)
(* 
fold_left_rev_right:
  forall [A B : Type] (f : A -> B -> B) (l : list A) (i : B),
  fold_right f i (rev l) = fold_left (fun (x : B) (y : A) => f y x) l i *)


Import ListNotations. 
From Coq Require Import FunctionalExtensionality.
From CDF Require Import CommonDefinitions.
(* From CDF Require Import Sequences. *)
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter_PUSH_POP_defs.
Module PP := SCORE_interpreter_PUSH_POP_defs.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*  ********************* *)
(** ** Interpreter [eval] *)
(*  ********************* *)

Fixpoint eval (P: com) (s: store) : store :=
  match P with
  | SKIP  => s
  | PUSH x => let (vp,c) := (fst (s x), snd (s x))
              in let (v,p) := (fst vp, snd vp)
              in update x (push (s x)) s
  | POP x => let (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x (pop (s x)) s 
  | DEC x => let (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x ((-1) + v, p, c) s
  | INC x => let   (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x (1 + v, p, c) s
  | SEQ P Q => (eval Q) (eval P s)
  | FOR x P => let v     := fst (fst (s x)) in
               let vIter := match (Z.compare v 0) with
                            | Lt => -v
                            | _  =>  v
                            end in
               let fIter := match (Z.compare v 0) with 
                            | Lt => fun s' => evalI P s'
                            | _  => fun s' => eval  P s' 
                            end in
               Z.iter vIter fIter s
  end
with evalI (P: com) (s: store) : store :=
  match P with
  | SKIP  => s
  | PUSH x => let (vp,c) := (fst (s x), snd (s x))
              in let (v,p) := (fst vp, snd vp)
              in update x (pop (s x)) s
  | POP x => let (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x (push (s x)) s
  | DEC x => let (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x (1 + v, p, c) s  
  | INC x => let (vp,c) := (fst (s x), snd (s x))
             in let (v,p) := (fst vp, snd vp)
             in update x ((-1) + v, p, c) s
  | SEQ P Q => (evalI P) (evalI Q s)
  | FOR x P => let v     := fst (fst (s x)) in
               let vIter := match (Z.compare v 0) with
                            | Lt => Z.opp v
                            | _  =>       v
                            end in
               let fIter := match (Z.compare v 0) with 
                            | Lt => fun s' => eval  P s' 
                            | Eq => fun s' => s' 
                            | Gt => fun s' => evalI P s'
                            end in
               Z.iter vIter fIter s
  end .

(*  ***************************** *)
(** *** [SEQ]-related properties  *)
(*  ***************************** *)
Lemma assoc_SEQ: forall P Q R s, 
  eval (SEQ (SEQ P Q) R) s = eval (SEQ P (SEQ Q R)) s.
Proof. intros.
repeat (rewrite eval_unfold_SEQ). reflexivity.
Qed.

Lemma eval_unfold_SEQ: forall P Q s, 
  eval (SEQ P Q) s = eval Q (eval P s).
Proof. unfold eval. fold eval. reflexivity.
Qed.

Lemma eval_fold_SEQ: forall P Q s,
  eval Q (eval P s) = eval (SEQ P Q) s.
Proof. intros. rewrite eval_unfold_SEQ. reflexivity.
Qed.

Lemma evalI_unfold_SEQ: forall P Q s, 
  evalI (SEQ P Q) s = evalI P (evalI Q s).
Proof. unfold evalI. fold evalI. reflexivity.
Qed.

Lemma evalI_fold_SEQ: forall P Q s,
  evalI P (evalI Q s) = evalI (SEQ P Q) s.
Proof. intros. rewrite evalI_unfold_SEQ. reflexivity.
Qed.

(*  ************************ *)
(** *** [FOR]-related unfold *)
(*  ************************ *)

(** **** Rewrite [FOR x P] to [Z.iter] *)
(** The properties of this section explicitly assume that [s x]
has the right structure and that the value of the current value
of [s x] is known.
*)

(** ****
  MATTEO: per ogni lemma che fa gli eval del for ho aggiunto
  la corrispettiva che fa gli unfold dell'evalI
**** **)

Lemma FOR_to_Ziter_Lt: forall s x P v p c, 
  s x = (v, p, c) -> v < 0 -> 
  eval (FOR x P) s = Z.iter (Z.opp v) (fun s' => evalI P s') s .
Proof. intros s x P v p c Eqsx VLt0.
unfold eval. unfold fst. rewrite Eqsx. rewrite VLt0.
  unfold Z.iter. reflexivity.
Qed.

Lemma FOR_to_Ziter_Lt_evalI: forall s x P v p c, 
  s x = (v, p, c) -> v < 0 -> 
  evalI (FOR x P) s = Z.iter (Z.opp v) (fun s' => eval P s') s .
Proof. intros s x P v p c Eqsx VLt0.
unfold evalI. unfold fst. rewrite Eqsx. rewrite VLt0.
  unfold Z.iter. reflexivity.
Qed.

Lemma FOR_to_Ziter_Gt: forall s x P v p c, 
  s x = (v, p, c) -> v > 0 -> 
  eval (FOR x P) s = Z.iter v (fun s' => eval  P s') s.
Proof. intros s x P v p c Eqsx VGt0.
unfold eval. unfold fst. rewrite Eqsx. rewrite VGt0.
  unfold Z.iter. reflexivity.
Qed.

Lemma FOR_to_Ziter_Gt_evalI: forall s x P v p c, 
  s x = (v, p, c) -> v > 0 -> 
  evalI (FOR x P) s = Z.iter v (fun s' => evalI  P s') s.
Proof. intros s x P v p c Eqsx VGt0.
unfold evalI. unfold fst. rewrite Eqsx. rewrite VGt0.
  unfold Z.iter. reflexivity.
Qed.

Lemma FOR_to_Ziter_Eq: forall s x P v p c, 
  s x = (v, p, c) -> v = 0 ->
    eval (FOR x P) s = s.
Proof. intros s x P v p c Eqsx VEq0.
unfold eval. unfold fst. rewrite Eqsx. rewrite VEq0. 
  simpl. reflexivity.
Qed.

Lemma FOR_to_Ziter_Eq_evalI: forall s x P v p c, 
  s x = (v, p, c) -> v = 0 ->
    evalI (FOR x P) s = s.
Proof. intros s x P v p c Eqsx VEq0.
unfold evalI. unfold fst. rewrite Eqsx. rewrite VEq0. 
  simpl. reflexivity.
Qed.

(*  *********************************** *)
(** **** Rewrite [Z.iter] to [Pos.iter] *)
(*  *********************************** *)

(** The properties of this section explicitly assume that the value
driving [Z.iter] is known.
*)
Lemma Ziter_to_Positer_Lt: forall (s:store) v,
  v < 0 -> 
    forall f, Z.iter (Z.opp v) f s = Pos.iter f s (Z.to_pos (Z.opp v)).
Proof. intros s v VLt0 f.
destruct v as [  | vGt0 | vEq0 ].
- lia.
- lia.
- unfold Z.opp. reflexivity.
Qed.

Lemma Ziter_to_Positer_Gt: forall (s:store) v,
  v > 0 -> 
    forall f, Z.iter v f s = Pos.iter f s (Z.to_pos v).
Proof. intros s v VGt0 f.
destruct v as [  | vGt0 | vEq0 ].
- lia.
- reflexivity.
- lia.
Qed.

Lemma Ziter_to_Positer_Eq: forall (s:store) f, 
  Z.iter 0 f s = s.
Proof. reflexivity. Qed.

(*  ******************************************* *)
(** **** Rewrite [eval (FOR ...)] to [Pos.iter] *)
(*  ******************************************* *)

(** The properties of this section explicitly assume that [s x]
has the right structure and that the value of the current value
of [s x] is known.
*)
Proposition eval_unfold_FOR_Lt: forall s x v p c, 
  s x = (v, p, c) -> v < 0 -> forall P,
  (eval (FOR x P) s = 
    Pos.iter (fun s' => evalI P s') s (Z.to_pos (Z.opp v))).
Proof. intros s x v p c Hsx VLt0 P.
destruct v as [ | vGt0 | vEq0 ].
- (* v < 0 *) lia.
- (* v > 0 *) lia.
- (* v = 0 *)
  (* Check (FOR_to_Ziter_Lt s x P (Z.neg vEq0) p c Hsx VLt0). *)
  rewrite (FOR_to_Ziter_Lt s x P (Z.neg vEq0) p c Hsx VLt0).
  apply Ziter_to_Positer_Lt. assumption.
Qed.

Proposition evalI_unfold_FOR_Lt: forall s x v p c, 
  s x = (v, p, c) -> v < 0 -> forall P,
  (evalI (FOR x P) s = 
    Pos.iter (fun s' => eval P s') s (Z.to_pos (Z.opp v))).
Proof. intros s x v p c Hsx VLt0 P.
destruct v as [ | vGt0 | vEq0 ].
- (* v < 0 *) lia.
- (* v > 0 *) lia.
- (* v = 0 *)
  (* Check (FOR_to_Ziter_Lt s x P (Z.neg vEq0) p c Hsx VLt0). *)
  rewrite (FOR_to_Ziter_Lt_evalI s x P (Z.neg vEq0) p c Hsx VLt0).
  apply Ziter_to_Positer_Lt. assumption.
Qed.

Proposition eval_unfold_FOR_Gt: forall s x v p c, 
  s x = (v, p, c) -> v > 0 -> forall P,
  (eval (FOR x P) s = 
    Pos.iter (fun s' => eval  P s') s (Z.to_pos v)) .
Proof. intros s x v p c Hsx VGt0 P.
destruct v as [ | vGt0 | vEq0 ].
- (* v < 0 *) lia.
- (* v > 0 *)
  (* Check (FOR_to_Ziter_Gt s x P (Z.pos vGt0) p c Hsx VGt0). *)
  rewrite (FOR_to_Ziter_Gt s x P (Z.pos vGt0) p c Hsx VGt0).
  apply Ziter_to_Positer_Gt. assumption.
- (* v = 0 *) lia.
Qed.

Proposition evalI_unfold_FOR_Gt: forall s x v p c, 
  s x = (v, p, c) -> v > 0 -> forall P,
  (evalI (FOR x P) s = 
    Pos.iter (fun s' => evalI  P s') s (Z.to_pos v)) .
Proof. intros s x v p c Hsx VGt0 P.
destruct v as [ | vGt0 | vEq0 ].
- (* v < 0 *) lia.
- (* v > 0 *)
  (* Check (FOR_to_Ziter_Gt s x P (Z.pos vGt0) p c Hsx VGt0). *)
  rewrite (FOR_to_Ziter_Gt_evalI s x P (Z.pos vGt0) p c Hsx VGt0).
  apply Ziter_to_Positer_Gt. assumption.
- (* v = 0 *) lia.
Qed.

Proposition eval_unfold_FOR_Eq: forall s x v p c, 
  s x = (v, p, c) -> v = 0 -> forall P,
    eval (FOR x P) s = s.
Proof. intros s x v p c Hsx VEq0 P.
(* Check (FOR_to_Ziter_Eq s x P v p c Hsx VEq0). *)
apply (FOR_to_Ziter_Eq s x P v p c Hsx VEq0).
Qed.

Proposition evalI_unfold_FOR_Eq: forall s x v p c, 
  s x = (v, p, c) -> v = 0 -> forall P,
    evalI (FOR x P) s = s.
Proof. intros s x v p c Hsx VEq0 P.
(* Check (FOR_to_Ziter_Eq s x P v p c Hsx VEq0). *)
apply (FOR_to_Ziter_Eq_evalI s x P v p c Hsx VEq0).
Qed.

(** ****
  MATTEO: Versione dimostrata del lemma che
    afferma che se delle variabili di un programma NON sono in
    vars_wr allora non vengono modificate.

    Nota che per avere abbastanza carico induttivo deve lavorare
    contemporaneamente su eval ed evalI.
    Inoltre non parla solo del for ma di tutti i programmi.
**** **)

Lemma non_wrvars_preserved : forall P x,
  ~ (In x (vars_wr P)) ->
  forall s, (eval P s) x = s x /\ (evalI P s) x = s x.
Proof. 
intros P x HxNotWr. 
induction P.
1 : { intro.
  simpl.
  apply conj;
  reflexivity. }
1-4 : intro.
1-4 : simpl.
1-4 : simpl in HxNotWr.
1-4 : apply Decidable.not_or in HxNotWr.
1-4 : destruct HxNotWr.
1-4 : repeat rewrite update_other.
all: try auto.
+ intro s.
  simpl.
  simpl in HxNotWr.
  rewrite (in_app_iff) in HxNotWr.
  apply Decidable.not_or in HxNotWr.
  destruct HxNotWr as (HxNotWrL, HxNotWrR).
  apply conj.
  * rewrite (proj1 (IHP2 HxNotWrR (eval P1 s))).
    rewrite (proj1 (IHP1 HxNotWrL s)).
    reflexivity.
  * rewrite (proj2 (IHP1 HxNotWrL (evalI P2 s))).
    rewrite (proj2 (IHP2 HxNotWrR s)).
    reflexivity.
+ intro.
  simpl in HxNotWr.
  assert (forall s : store, eval P s x = s x) as IHPL. {
    intro s'.
    rewrite (proj1 (IHP HxNotWr s')).
    reflexivity.
  }
  assert (forall s : store, evalI P s x = s x) as IHPR. {
    intro s'.
    rewrite (proj2 (IHP HxNotWr s')).
    reflexivity.
  }
  destruct (s x0) as ((vx0, lx0), ex0) eqn:Hsx0.
  destruct vx0 eqn:Hvx0.
  * assert (eval (FOR x0 P) s = s) as HforEq. {
      apply (eval_unfold_FOR_Eq s x0 0 lx0 ex0 Hsx0).
      reflexivity.
    }
    assert (evalI (FOR x0 P) s = s) as HforEq_evalI. {
      apply (FOR_to_Ziter_Eq_evalI s x0 P vx0 lx0 ex0).
      - rewrite Hsx0. rewrite Hvx0. reflexivity.
      - assumption.
    }
    rewrite HforEq.
    rewrite HforEq_evalI.
    tauto.
  * (* Search eval. *)
    assert (
      eval (FOR x0 P) s = 
        Pos.iter (fun s' : store => eval P s') s (Z.to_pos vx0)). {
      apply (eval_unfold_FOR_Gt s x0 vx0 lx0 ex0).
      - rewrite Hsx0. rewrite Hvx0. reflexivity.
      - rewrite Hvx0. apply Zgt_pos_0.
    }
    assert (
      evalI (FOR x0 P) s = 
        Pos.iter (fun s' : store => evalI P s') s (Z.to_pos vx0)). {
      apply (evalI_unfold_FOR_Gt s x0 vx0 lx0 ex0).
      - rewrite Hsx0. rewrite Hvx0. reflexivity.
      - rewrite Hvx0. apply Zgt_pos_0.
    }
    rewrite H.
    rewrite H0.
    apply conj.
    - apply Pos.iter_invariant.
      -- intro s'.
      intro Hs'x.
      simpl in HxNotWr.
      (* Check (IHP HxNotWr s').  *)
      rewrite (proj1 (IHP HxNotWr s')). 
      rewrite Hs'x.
      reflexivity.
      -- reflexivity.
    - apply Pos.iter_invariant.
      -- intro s'.
      intro Hs'x.
      simpl in HxNotWr.
      (* Check (IHP HxNotWr s').  *)
      rewrite (proj2 (IHP HxNotWr s')). 
      rewrite Hs'x.
      reflexivity.
      -- reflexivity.
  * (* Search eval. *)
    assert (
      eval (FOR x0 P) s = 
        Pos.iter (fun s' : store => evalI P s') s (Z.to_pos (- (Z.neg p)))). {
      apply (eval_unfold_FOR_Lt s x0 (Z.neg p) lx0 ex0 Hsx0).
      apply Zlt_neg_0.
    }
    assert (
      evalI (FOR x0 P) s = 
        Pos.iter (fun s' : store => eval P s') s (Z.to_pos (- (Z.neg p)))). {
      apply (evalI_unfold_FOR_Lt s x0 (Z.neg p) lx0 ex0 Hsx0).
      apply Zlt_neg_0.
    }
    apply conj.
    - rewrite H.
      rewrite <- Hvx0.
      apply Pos.iter_invariant.
      -- intro s'.
         intro Hs'x.
         simpl in HxNotWr.
         rewrite (proj2 (IHP HxNotWr s')). 
         rewrite Hs'x.
         reflexivity.
      -- reflexivity.
    - rewrite H0.
        rewrite <- Hvx0.
        apply Pos.iter_invariant.
        -- intro s'.
           intro Hs'x.
           simpl in HxNotWr.
           rewrite (proj1 (IHP HxNotWr s')). 
           rewrite Hs'x.
           reflexivity.
        -- reflexivity.
Qed.

(** **** 
  MATTEO: I seguenti due lemmi spezzano il lemma precedente in 
    due lemmi, per renderne più facile l'applicazione. 
    Il primo parla di eval e l'altro di evalI. 
**** **)

Lemma non_wrvars_preserved_eval : forall P x,
  ~ (In x (vars_wr P)) ->
  forall s, (eval P s) x = s x.
Proof.
intros.
apply non_wrvars_preserved.
assumption.
Qed.

Lemma non_wrvars_preserved_evalI : forall P x,
  ~ (In x (vars_wr P)) ->
  forall s, (evalI P s) x = s x.
Proof.
intros.
apply non_wrvars_preserved.
assumption.
Qed.

(*  *********************************************************** *)
(** **** Given only [s x], rewrite [eval (FOR ...)] to [Z.iter] *)
(*  *********************************************************** *)

(** The properties of this section explicitly assume that [s x]
has the right structure but the value of the current value of [s x] 
is unknown.
*)
Lemma FOR_to_Ziter_impl_OR: forall s x v p c, 
  s x = (v, p, c) -> (forall P, 
     eval (FOR x P) s = Z.iter (Z.opp v) (fun s' => evalI P s') s \/  
     eval (FOR x P) s = Z.iter (      v) (fun s' => eval  P s') s \/
     eval (FOR x P) s = s  ).
Proof. intros s x v p c Hsx. 
assert (Vcases:  {v < 0} + {v > 0} + {v = 0}).
  { apply Z_dec. }
destruct Vcases as [ [ VLt0 | VGt0] | VEq0 ].
- intro P. left . apply (FOR_to_Ziter_Lt s x P v p c Hsx VLt0).
- intro P. right. left. apply (FOR_to_Ziter_Gt s x P v p c Hsx VGt0).
- intro P. right. right. apply (FOR_to_Ziter_Eq s x P v p c Hsx VEq0).
Qed.

Proposition eval_unfold_FOR_impl_OR: forall s x v p c, 
  s x = (v, p, c) -> forall P,
  (eval (FOR x P) s = 
    Pos.iter (fun s' => evalI P s') s (Z.to_pos (Z.opp v))) \/
  (eval (FOR x P) s = 
    Pos.iter (fun s' => eval  P s') s (Z.to_pos        v))  \/
  (eval (FOR x P) s = s) .
Proof. intros s x v p c Hsx P.
assert (Vcases: {v < 0} + {v > 0} + {v = 0}).
  { apply Z_dec. }
destruct Vcases as [ [ VLt0 | VGt0] | VEq0 ].
- (* vx < 0 *) left. 
  apply (eval_unfold_FOR_Lt s x v p c Hsx VLt0 P).
- (* vx > 0 *) right. left.
  apply (eval_unfold_FOR_Gt s x v p c Hsx VGt0 P).
- (* vx = 0 *) right. right.
apply (eval_unfold_FOR_Eq s x v p c Hsx VEq0 P).
Qed.


(** **** ewrite [eval (FOR ...)] to [Z.iter] with no assumotions *)

(** The properties do not assume anything on [s x] and yields a disjunction of alternatives.

The property that we might give name [FOR_to_Positer_OR] currently is not present.
*)
Lemma FOR_to_Ziter_OR: forall s x P, 
  eval (FOR x P) s = Z.iter (-(fst (fst (s x)))) (fun s' => evalI P s') s  \/ 
  eval (FOR x P) s = Z.iter (fst (fst (s x))) (fun s' => eval  P s') s \/
  eval (FOR x P) s = s .
Proof. intros s x P.
assert (Hsx: exists v p c, s x = (v, p, c)).
{ destruct (s x) as ((v, p), c). 
  exists v. exists p. exists c. reflexivity. }
destruct Hsx as (v, (p, (c, Eqsx))).
rewrite Eqsx. unfold fst.  
assert (Vcases:  {v < 0} + {v > 0} + {v = 0}).
  { apply Z_dec. }
destruct Vcases as [ [ VLt0 | VGt0] | VEq0 ].
- (* vx < 0 *) left.  
  apply (FOR_to_Ziter_Lt s x P v p c Eqsx VLt0).  
- (* vx > 0 *) right. left. 
  apply (FOR_to_Ziter_Gt s x P v p c Eqsx VGt0).  
- (* vx = 0 *) right. right. 
  apply (FOR_to_Ziter_Eq s x P v p c Eqsx VEq0). 
Qed.

Lemma Ziter_to_Positer_OR: forall (s:store) x f, 
  Z.iter (Z.opp (fst (fst (s x)))) f s = Pos.iter  f s (Z.to_pos (Z.opp (fst (fst (s x))))) \/
  Z.iter (fst (fst (s x))) f s = Pos.iter  f s (Z.to_pos (fst (fst (s x)))) \/
  Z.iter 0 f s = s.
Proof. intros s x f.
assert (Hsx: exists v p c, s x = (v, p, c)).
{ destruct (s x) as ((v, p), c). 
  exists v. exists p. exists c. reflexivity. }
destruct Hsx as (v, (p, (c, Eqsx))).
rewrite Eqsx. unfold fst.  
assert (Vcases:  {v < 0} + {v > 0} + {v = 0}).
  { apply Z_dec. }
destruct Vcases as [ [ VLt0 | VGt0] | VEq0 ].
- (* vx < 0 *) left.
  apply (Ziter_to_Positer_Lt s v VLt0 f).
- (* vx > 0 *) right. left. 
  apply (Ziter_to_Positer_Gt s v VGt0 f).
- (* vx = 0 *) right. right. 
  apply (Ziter_to_Positer_Eq s f). 
Qed.

(* Check (@Pos.iter store). *)
(* Check Pos_iter_id. *)
(* Check (Pos.iter_ind store (fun s' : store => s')). *)
(* forall (A : Type) 
          (f : A -> A) 
          (a : A) 
          (P : positive -> A -> Prop),
   P 1%positive (f a) 
-> (forall (p : positive) (a' : A), P p a' -> P (Pos.succ p) (f a')) 
-> forall p : positive, P p (Pos.iter f a p) *)
(* Check Z.iter. *)
(* Locate "-"%Z. *)
(* Check Z.opp. *)
(* Compute (Z.opp (Z.opp 1)). *)
