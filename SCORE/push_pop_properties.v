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
(** * PUSH and POP: 4 cases version *)

Lemma pu_inv_po : forall (x: Z * list Z * nat), 
  pu (po x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.


Lemma po_inv_pu : forall (x: Z * list Z * nat), 
  po (pu x) = x.
Proof. intro p. destruct p as ((v, s), c).
destruct v as [ | vp | vn ].
- (* v = 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v > 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
- (* v < 0 *)
  destruct c as [ | c' ].
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
  + destruct s as [ | h t ].
    * simpl. reflexivity. 
    * unfold po; 
      destruct h as [ | hp | hn ];
      destruct t as [ | h' t']; 
      reflexivity.
Qed.

Theorem po_inv_pu_inv_po : forall p : Z * list Z * nat, 
  (po (pu p) = p) /\ (pu (po p) = p).
Proof. destruct p as ((v, s), c). intros. 
split.
- apply po_inv_pu.
- apply pu_inv_po.
Qed.


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

