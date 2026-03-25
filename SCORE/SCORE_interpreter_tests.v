From Coq Require Import Arith ZArith Lia Bool String List Program.Equality.
Import ListNotations.
From Coq Require Import FunctionalExtensionality.
From CDF Require Import Sequences.
From CDF Require Import SCORE_language.
From CDF Require Import SCORE_interpreter.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Definition emptyStore : store :=
fun y => [] .

Definition myStore : store :=
update "z" [3] (
update "y" [2] (
update "x" [1] emptyStore)) .

Definition myStoreNeg : store :=
update "z" [-3] (
update "y" [-2] (
update "x" [-1] emptyStore)) .

Eval compute in (eval SKIP myStore) "z".
Eval compute in (eval SKIP myStore) "x".
Eval compute in (eval SKIP myStore) "w".

Eval compute in (eval (INC "z") myStore) "z".
Eval compute in (eval SKIP myStore) "z".
Eval compute in (eval (INC "x") myStore) "x".
Eval compute in (eval SKIP myStore) "x".
Eval compute in (eval (INC "x";; DEC "x") myStore) "x".
Eval compute in (eval SKIP myStore) "x".

Eval compute in (eval (INC "x") myStoreNeg) "x".
Eval compute in (eval SKIP myStoreNeg) "x".
Eval compute in (eval (INC "x";; DEC "x") myStoreNeg) "x".
Eval compute in (eval SKIP myStoreNeg) "x".

Eval compute in (eval (FOR "x" (DEC "y")) myStore) "y".
Eval compute in (eval SKIP myStore) "x".
Eval compute in (eval SKIP myStore) "y".

Eval compute in (eval (FOR "z" (INC "y")) myStoreNeg) "y".
Eval compute in (eval SKIP myStoreNeg) "z".
Eval compute in (eval SKIP myStoreNeg) "y".

Definition myStoreASNTst00 := 
     eval (CON "x";; FOR "z" (INC "x");; FOR "x" (DEC "z")) myStore.
Eval compute in myStoreASNTst00 "x".
Eval compute in myStoreASNTst00 "y".
Eval compute in myStoreASNTst00 "z".

Definition myStoreNegASNTst00 := 
     eval (CON "x";; FOR "z" (DEC "x");; FOR "x" (INC "z")) myStoreNeg.
Eval compute in myStoreNegASNTst00 "x".
Eval compute in myStoreNegASNTst00 "y".
Eval compute in myStoreNegASNTst00 "z".
