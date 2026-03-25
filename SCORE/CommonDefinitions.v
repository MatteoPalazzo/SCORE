From Coq Require Import String List ZArith Lia.
From Coq Require Import BinNums.
From Coq Require Import BinInt.
From Coq Require Import ZArith.Zmisc.
From Coq Require Import Arith.Wf_nat.
From Coq Require Import ZArith.Int.
From Coq Require Import PArith.BinPos.

Definition ident := string.
Definition symtab : Type := ident -> ident * ident.

Open Scope string_scope.

Definition stEmpty : symtab := fun _ => (EmptyString, EmptyString).
Definition stTest : symtab := 
    fun x => if string_dec x "z" then ("z", "za")%string else 
             if string_dec x "y" then ("y", "ya")%string else
             if string_dec x "x" then ("x", "xa")%string else
             stEmpty x.

Ltac inv H := inversion H; clear H; subst.

Definition store {A: Type}: Type := ident -> A.

(** Store updating *)
Definition update {A: Type} (x: ident) (v: A) (s: store) : store := fun y => if string_dec x y then v else s y.

Lemma update_same: forall (A: Type) x v s, 
  (@update A x v s) x = v.
Proof. 
  intros. 
  unfold update. 
  destruct (string_dec x x).
  - reflexivity.
  - apply False_ind.
    apply n.
    reflexivity.
Qed.
(* ORI
Proof. unfold update; intros. destruct (string_dec x x); congruence. Qed. *)

Lemma update_other: forall (A: Type) x v s y, 
    x <> y -> (@update A x v s) y = s y.
Proof.
intros.
unfold update.  
destruct (string_dec x y).
- unfold not in H.
  apply False_ind.
  apply H.
  assumption.
- reflexivity.
Qed.

Lemma update_overwrite_var: forall A x u v s y,
(@update A x u ((@update A x v) s)) y = (@update A x u s) y.
Proof.
intros. unfold update.  
destruct (string_dec x y); reflexivity.
Qed.

Lemma update_same_var: forall A x s y,
(@update A x (s x) s) y = s y.
Proof.
intros. unfold update.  
destruct (string_dec x y).
- subst. reflexivity.
- reflexivity.
Qed.

(** **** Invertibility im general  *)
Definition injective {A B} (f : A -> B) :=
   forall x y : A , f x = f y -> x = y .

(* Check injective. *)

Definition surjective {A B} (f : A -> B) := forall b, exists a, f a = b.


Definition left_inverse {A B} (f : A -> B) g := forall a, g (f a) = a.

Definition right_inverse {A B} (f : A -> B) g := forall b, f (g b) = b.

Definition inverse {A B} (f : A -> B) g := left_inverse f g /\ right_inverse f g.

Lemma inverse_f_g_iff_inverse_g_f {A B}: 
  forall (f: A->B) (g: B->A), inverse f g <-> inverse g f.
Proof.
intros.
unfold inverse in *.
unfold left_inverse in *.
unfold right_inverse in *.
tauto.
Qed.

Local Open Scope positive_scope.

(* Theorem succ_iter_pos_id (n : positive) : succ_iter n = n + 1.
Proof.
unfold succ_iter.
apply Pos.iter_ind.
+ unfold my_succ. reflexivity.
+ intros.
  unfold my_succ.
  rewrite Pos.add_succ_l.
  rewrite <- Pos.add_1_r.
  rewrite <- H.
  reflexivity.
Qed. *)


Theorem iter_left_inverse_iter_function_id {A} : 
  forall (f : A -> A) (f_inv : A -> A), left_inverse f f_inv -> 
    forall (n : positive) (x : A), (Pos.iter f_inv (Pos.iter f x n) n) = x.
Proof.
intros f f_inv H0.
unfold left_inverse in H0.
intros n.
apply (Pos.peano_ind (fun n => (forall x, (Pos.iter f_inv (Pos.iter f x n) n) = x))).
+ intros.
  simpl. 
  rewrite (H0 x).
  reflexivity.
+ intros. 
  rewrite Pos.iter_succ.
  rewrite Pos.iter_succ_r.
  rewrite (H (f x)).
  rewrite (H0 x).
  reflexivity.
Qed.

Theorem iter_right_inverse_iter_function_id {A} : 
  forall (f : A -> A) (f_inv : A -> A), right_inverse f f_inv -> 
    forall (n : positive) (x : A), (Pos.iter f (Pos.iter f_inv x n) n) = x.
Proof.
intros f f_inv H0.
unfold right_inverse in H0.
intros n.
apply (Pos.peano_ind (fun n => (forall x, (Pos.iter f (Pos.iter f_inv x n) n) = x))).
+ intros.
  simpl. 
  rewrite (H0 x).
  reflexivity.
+ intros. 
  rewrite Pos.iter_succ.
  rewrite Pos.iter_succ_r.
  rewrite (H (f_inv x)).
  rewrite (H0 x).
  reflexivity.
Qed.

Theorem iter_inverse_iter_function_id {A} : 
  forall (f : A -> A) (f_inv : A -> A), inverse f f_inv -> 
    forall (n : positive) (x : A), (Pos.iter f_inv (Pos.iter f x n) n) = x.
Proof.
intros f f_inv H0.
unfold inverse in *.
destruct H0 as (H0L, H0R).
intros n.
apply (Pos.peano_ind (fun n => (forall x, (Pos.iter f_inv (Pos.iter f x n) n) = x))).
+ intros.
  simpl. 
  rewrite (H0L x).
  reflexivity.
+ intros. 
  rewrite Pos.iter_succ.
  rewrite Pos.iter_succ_r.
  rewrite (H (f x)).
  rewrite (H0L x).
  reflexivity.
Qed.
