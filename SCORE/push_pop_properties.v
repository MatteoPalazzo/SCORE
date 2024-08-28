From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

From CDF Require Import common_parts.
From CDF Require Import push_pop_definitions.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*  ******************************************** *)
(** * Proof of "push/pop are each other inverse" *)

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