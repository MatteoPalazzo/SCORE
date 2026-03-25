From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.

Import ListNotations. 
From Coq Require Import FunctionalExtensionality.
From CDF Require Import CommonDefinitions.
(* From CDF Require Import Sequences. *)
(* From CDF Require Import SCORE_language. *)
From CDF Require Import SCORE_interpreter_PUSH_POP_defs.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.


(* Require Import BinNums. *)

(*  ******************************************** *)
(** * Proof of "PUSH/POP are each other inverse" *)


Lemma push_inv_pop : forall (x: Z * list Z * nat), 
  push (pop x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.


Lemma pop_inv_push : forall (x: Z * list Z * nat), 
  pop (push x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.

Theorem pop_invertible : forall p : Z * list Z * nat, 
  (pop (push p) = p) /\ (push (pop p) = p).
Proof. destruct p as ((v, s), c). intros. 
split.
- apply pop_inv_push.
- apply push_inv_pop.
Qed.