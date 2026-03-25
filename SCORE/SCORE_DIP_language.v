From CDF Require Import CommonDefinitions.
From Coq Require Import ZArith Bool String List.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Declare Scope SCORE_scope.

(** * 1.  The SCORE language *)
Definition store : Type := @store (Z * list Z * nat).

Inductive com: list ident ->  Type :=
  | SKIP: com []
  | PUSH (x:ident): com [x] 
  | POP  (x:ident): com [x]
  | DEC  (x:ident): com [x]
  | INC  (x:ident): com [x]
  | SEQ  (P:com) (Q:com): com (lP ++ lQ)
  | FOR  (x:ident ) (P:com lP): com (x::lP)
  .

(** We write [P ;; Q] instead of [SEQ P Q]. *)
Infix ";;" := SEQ (at level 80, right associativity) : SCORE_scope.

(* written/writable variables *)
Fixpoint wvars (P: com): list ident :=
  match P with
  | SKIP => []
  | PUSH x => [x]
  | POP x => [x]
  | DEC x => [x]
  | INC x => [x]
  | SEQ P Q => (wvars P) ++ (wvars Q)
  | FOR x P => filter (fun y =>  negb (eqb x y)) (wvars P)
  end .

Compute (wvars (FOR "x" (SEQ (INC "x") (DEC "y")))).
Compute (wvars ((INC "x"))).

(* read-only variables *)
Fixpoint rovars (P: com): list ident :=
  match P with
  | FOR x P => x::(filter (fun y =>  negb (eqb x y)) (rovars P)) 
  | SEQ P Q => (rovars P) ++ (rovars Q)
  | _ => []
  end .

Compute (rovars (FOR "x" (SEQ (INC "x") (DEC "y")))).
Compute (rovars ((INC "x"))).


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

Lemma inv_self_dual: forall (P:com),
    inv (inv P) = P.
Proof. induction P.
- unfold inv. reflexivity.  
- unfold inv. reflexivity. 
- unfold inv. reflexivity.
- unfold inv. reflexivity.
- unfold inv. reflexivity.
- unfold inv. fold inv. 
  rewrite IHP1. rewrite IHP2.
  reflexivity.
- unfold inv. fold inv.
  rewrite IHP. reflexivity. 
Qed.

