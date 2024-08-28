From Coq Require Import String.

Definition ident := string.
Definition symtab : Type := ident -> ident * ident.

Open Scope string_scope.

Definition stEmpty : symtab := fun _ => (EmptyString, EmptyString).
Definition stTest : symtab := 
    fun x => if string_dec x "z" then ("z", "za")%string else 
             if string_dec x "y" then ("y", "ya")%string else
             if string_dec x "x" then ("x", "xa")%string else
             stEmpty x.

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
