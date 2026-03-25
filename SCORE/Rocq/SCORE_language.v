From CDF Require Import CommonDefinitions.
From Coq Require Import ZArith Bool String List.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Declare Scope SCORE_scope.

(*  ********************* *)
(** * 1.  S-CORE language *)
(*  ********************* *)
Definition store : Type := @store (Z * list Z * nat).

Inductive com: Type :=
  | SKIP                                          
  | PUSH (x: ident)         (**r  [l := 0::l] *)
  | POP (x: ident)          (**r  [l := t] if l==0::t *)        
  | DEC (x: ident)          (**r  [l := (x-1)::t] if l==x::t *)
  | INC (x: ident)          (**r  [l := (x+1)::t] if l==x::t *)
  | SEQ (P: com) (Q: com)   (**r  [P; Q]   *)        
  | FOR (x: ident) (P: com) (**r  P;;...;;P x times if l==x::t] *)
  .

(** We write [P ;; Q] instead of [SEQ P Q]. *)
Infix ";;" := SEQ (at level 80, right associativity) : SCORE_scope.

(** [sub_com] produces the list of striclty sub-commands
in a given [com]mand .*)
Fixpoint sub_com (P: com) : list com :=
  match P with
  | SEQ Q R => (sub_com Q) ++ (sub_com R)
  | FOR x Q => Q :: (sub_com Q)
  | _ => []
  end .

(* Lemma sub_com_test: sub_com (FOR "x" (FOR "y" (INC "z"))) = [FOR "y" (INC "z"); INC "z"].
Proof. simpl. reflexivity. Qed. *)


(*  *************************************** *)
(** *** Sintactically inverting a [com]mand *)
(*  *************************************** *)

(** [inv] inverts syntactically a given [com]mand [P]
*)
Fixpoint inv (P: com): com :=
  match P with
  | SKIP => SKIP                                          
  | PUSH x => POP x
  | POP x => PUSH x
  | DEC x => INC x
  | INC x => DEC x
  | SEQ P Q => SEQ (inv Q) (inv P)
  | FOR x P => FOR x (inv P) 
  end .

  (** The name [inv_self_dual] should be self-explaining *)
Lemma inv_self_dual: forall (P:com),
    inv (inv P) = P.
Proof. induction P.
6:{ unfold inv. fold inv. 
    rewrite IHP1. rewrite IHP2.
    reflexivity. }
6:{ unfold inv. fold inv.
    rewrite IHP. reflexivity. }
all: unfold inv.
all: reflexivity.
Qed.

(* *********************** *)
(** **** [inv] distributes *)
(* *********************** *)

(** It is useful to show that [inv]ersion distributes
over the composite [com]mands.
*)
Lemma inv_unfold_SEQ: forall P Q, 
  inv (SEQ P Q) = SEQ (inv Q) (inv P).
Proof. unfold inv. fold inv. reflexivity. Qed.

Lemma inv_fold_SEQ: forall P Q,
  SEQ (inv Q) (inv P) = inv (SEQ P Q).
Proof. intros. rewrite inv_unfold_SEQ. reflexivity.
Qed.

Lemma inv_unfold_FOR: forall x P, 
  inv (FOR x P) = FOR x (inv P).
Proof. unfold inv. fold inv. reflexivity. Qed.

Lemma inv_fold_FOR: forall x P,
  FOR x (inv P) = inv (FOR x P).
Proof. intros. rewrite inv_unfold_FOR. reflexivity.
Qed.


(*  ************************************ *)
(** *** Writable variable of a [com]mand *)
(*  ************************************ *)

(** Determining the set (list) of identifiers that any
[com]mand [P] can modify as effect of [PUSH, POP, ...]
will serve to identify those varaibles which are read-only.

We here define the list of [ident]ifiers that may be 
written, their relation on the sub-[com]mands and, finally,
[wfcom_rel_excludes_wr] which says that if a [com]mand [P]
is well-formed w.r.t. a variable name [x], then [P] cannot
write [x].
*)

(** [vars_wr] gives the list of writable variables in a 
[com]mand [P]. Namely it lists all the variable names of 
[vars] that in no case drive an iteration. For example,
if [FOR x Q] is a sub-[com]mand of [P], then [x] does
not occur in the list of [vars_w P].
*)
Fixpoint vars_wr (P: com): list ident :=
  match P with
  | SKIP => []
  | PUSH x => [x]
  | POP x => [x]
  | DEC x => [x]
  | INC x => [x]
  | SEQ P Q => (vars_wr P) ++ (vars_wr Q)
  | FOR x P => vars_wr P
  end .

(** [wfcom_rel P x] is the well-formedness of a [com]mand [P]
relative to a given variable (name) [x]. 
[wlcom_rel P x] yields [True] if none of the [com]mands in [P]
writes [x].
 *)
Fixpoint wfcom_rel (P: com) (x: ident) : Prop :=
  match P with
  | SKIP => True
  | PUSH y => x <> y
  | POP y => x <> y
  | DEC y => x <> y
  | INC y => x <> y
  | SEQ P Q => (wfcom_rel P x) /\ (wfcom_rel Q x)
  | FOR y Q => wfcom_rel Q x
  end .


(** [vars] gives the lists of variables in a [com]mand. *)
Fixpoint vars (P: com): list ident :=
  match P with
  | SKIP => []
  | PUSH x => [x]
  | POP x => [x]
  | DEC x => [x]
  | INC x => [x]
  | SEQ P Q => (vars P) ++ (vars Q)
  | FOR x P => x::(vars P)
  end .

(** [wfcom] yields [True] if the [com]mand it is applied to
is globally well-formed: for every sub-[com]mand [FOR x P], 
the name [x] does not belong to the [vars] of [P].
*)
 Fixpoint wfcom (P: com): Prop :=
  match P with
  | SEQ P Q => (wfcom P) /\ (wfcom Q)
  | FOR x P => (wfcom P) /\ (not (In x (vars_wr P)))
  | _ => True
  end .
