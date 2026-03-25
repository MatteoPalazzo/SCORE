From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import List.
Import ListNotations. 

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(*  ******************************** *)
(** * PUSH and POP: two versions     *)
(** We hereby presents two versions  
    of the same functions PUSH and
    POP. The first pair (pop, push)
    is the one presented in the paper 
    "Reversible Computation with 
    Stacks and 'Reversible Management 
    of Failures'"; the second one 
    (pop4, push4)
    is an extended more detailed
    version.                         *)

(*  ******************************** *)
(** ** PUSH and POP: 3 cases version *)

Definition pop (st : Z * (list Z) * nat) : Z * (list Z) * nat := 
match st with 
| (0, v::t,   O) => (v,    t,   O)
| (0, v::t, S c) => (0, v::t, S c)
| (v,    s,   c) => (v,    s, S c)
end.

Definition push (st : Z * list Z * nat) : (Z * list Z * nat) := 
match st with 
| (v,    t,   O) => (0, v::t,   O) 
| (0, v::t, S c) => (0, v::t, S c)
| (v,    s, S c) => (v,    s,   c)
end.

(*  ******************************** *)
(** ** PUSH and POP: 4 cases version *)

Definition pop4 (p : Z * list Z * nat) : Z * list Z * nat := 
match p with 
| (v,   [],   n) => (v,   [], S n)
| (0, v::t,   O) => (v,    t,   O)
| (0, v::t, S n) => (0, v::t, S n)
| (k, v::t,   n) => (k, v::t, S n)
end.

(** Intution about the definition of [pop4]:
- [pop4 (v,[],n) = (v,[],S n)] manages the first attempt to eliminate the top in an empty list. That is not possible and the counter counts that attempt;
- [pop4 (0,v::t,O) = (v,t,0)] correctly eliminates the top of a stack because: (i) there is no trace of wrong attempts in the counter, (ii) the current value being overwritten is 0;
- [pop4 (0,v::t,S n) = (0, v::t, S n)] does not allow to eliminate the top of the stack because there are previous wrong attemnpts to forget the top, even if the current value of the variable is 0 and it could be  forgotten;
- [pop4 (k,v::t,n) = (k, v::t, S n)], like in the previous case, it is not possible to eliminate the top of the stack when there are previous wrong attemnpts to forget the top. Moreover, since the current value of the variable is not 0 this is a further wrong attempt to discard the top of the stack. The counter keeps track of it.
*)

Definition push4 (p : Z * list Z * nat) : (Z * list Z * nat) := 
match p with 
| (v,   [], S n) => (v,   [],   n)
| (v,    t,   O) => (0, v::t,   O) 
| (0, v::t, S n) => (0, v::t, S n)
| (k, v::t, S n) => (k, v::t,   n) 
end.

(** The definition of [push4], "complements" the one of [pop4], the "main" case being [pop4 (v,t,O) = (0,v::t,O)] which stores the current value of the variable on top of the stack, resetting it to 0, because no there is no trace of some pending wrong occurrence of [po].
*)

