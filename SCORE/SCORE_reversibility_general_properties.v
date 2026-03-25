From CDF Require Import SCORE_interpreter . 
From CDF Require Import SCORE_language.

From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Open Scope SCORE_scope.

Lemma evalI_to_eval_inv : 
  forall P s, evalI P s = eval (inv P) s /\ eval P s = evalI (inv P) s.
Proof.
induction P.
1-5: simpl; tauto.
+ intro.
  simpl.
  rewrite (proj1 (IHP2 s)).
  rewrite (proj1 (IHP1 (eval (inv P2) s))).
  rewrite (proj2 (IHP1 s)).
  rewrite (proj2 (IHP2 (evalI (inv P1) s))).
  tauto.
+ intro.
  split.
  all: apply functional_extensionality;
  destruct (s x) as ((vx, lx), ex) eqn:Hsx;
  rewrite (inv_unfold_FOR);
  destruct vx.
  * rewrite (evalI_unfold_FOR_Eq s x 0 lx ex).
    rewrite (eval_unfold_FOR_Eq s x 0 lx ex).
    all: auto.
  * rewrite (evalI_unfold_FOR_Gt s x (Z.pos p) lx ex).
    rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx ex).
    set (fEvalI := fun s' : store => evalI P s').
    set (fEval := fun s' : store => eval (inv P) s').
    assert (fEvalI = fEval) as Heq. {
      unfold fEvalI. unfold fEval.
      apply functional_extensionality.
      intro. 
      exact (proj1 (IHP x0)).
    }
    rewrite Heq. reflexivity.
    all: auto.
    all: apply Zgt_pos_0.
  * rewrite (evalI_unfold_FOR_Lt s x (Z.neg p) lx ex).
    rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx ex).
    set (fEval := fun s' : store => eval P s').
    set (fEvalI := fun s' : store => evalI (inv P) s').
    assert (fEvalI = fEval) as Heq. {
      unfold fEvalI. unfold fEval.
      apply functional_extensionality.
      intro. symmetry.
      exact (proj2 (IHP x0)).
    }
    rewrite Heq. reflexivity.
    all: auto.
    all: apply Zlt_neg_0.
  * rewrite (evalI_unfold_FOR_Eq s x 0 lx ex).
    rewrite (eval_unfold_FOR_Eq s x 0 lx ex).
    all: auto.
  * rewrite (evalI_unfold_FOR_Gt s x (Z.pos p) lx ex).
    rewrite (eval_unfold_FOR_Gt s x (Z.pos p) lx ex).
    set (fEval := fun s' : store => eval P s').
    set (fEvalI := fun s' : store => evalI (inv P) s').
    assert (fEvalI = fEval) as Heq. {
      unfold fEvalI. unfold fEval.
      apply functional_extensionality.
      intro. symmetry. 
      exact (proj2 (IHP x0)).
    }
    rewrite Heq. reflexivity.
    all: auto.
    all: apply Zgt_pos_0.
  * rewrite (evalI_unfold_FOR_Lt s x (Z.neg p) lx ex).
    rewrite (eval_unfold_FOR_Lt s x (Z.neg p) lx ex).
    set (fEvalI := fun s' : store => evalI P s').
    set (fEval := fun s' : store => eval (inv P) s').
    assert (fEvalI = fEval) as Heq. {
      unfold fEvalI. unfold fEval.
      apply functional_extensionality.
      intro.
      exact (proj1 (IHP x0)).
    }
    rewrite Heq. reflexivity.
    all: auto.
    all: apply Zlt_neg_0.
Qed.