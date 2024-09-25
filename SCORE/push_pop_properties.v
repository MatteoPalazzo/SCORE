From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations.

From CDF Require Import push_pop_definitions.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*  ******************************************** *)
(** * Proof of "push/pop are each other inverse" *)

(*  ******************************** *)
(** * PUSH and POP: 3 cases version *)


Lemma push_inv_pop : forall (st: Z * list Z * nat), 
  push (pop st) = st.
Proof. intro st. destruct st as ((v, s), c).
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

Lemma pop_inv_push : forall (st: Z * list Z * nat), 
  pop (push st) = st.
Proof. intro st. destruct st as ((v, s), c).
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

Theorem pop_inv_push_inv_pop : forall p : Z * list Z * nat, 
  (pop (push p) = p) /\ (push (pop p) = p).
Proof. destruct p as ((v, s), c). intros. 
split.
- apply pop_inv_push.
- apply push_inv_pop.
Qed.

(*  ******************************** *)
(** * PUSH and POP: 4 cases version *)

Lemma push4_inv_pop4 : forall (x: Z * list Z * nat), 
  push4 (pop4 x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.


Lemma pop4_inv_push4 : forall (x: Z * list Z * nat), 
  pop4 (push4 x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold pop4; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.

Theorem pop4_inv_push4_inv_pop4 : forall p : Z * list Z * nat, 
  (pop4 (push4 p) = p) /\ (push4 (pop4 p) = p).
Proof. destruct p as ((v, s), c). intros. 
split.
- apply pop4_inv_push4.
- apply push4_inv_pop4.
Qed.




