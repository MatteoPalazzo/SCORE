From CDF Require Import SCORE_language.

From Coq Require Import ZArith Bool String List.
Import ListNotations.

Open Scope SCORE_scope.

(** [wfcom_rel] is down-ward closed. If a [com]mand [P] is
sell-formed relatively to a variable name [x], all the 
sub-[com]mmand of [P] are sell-formed relatively to [x].
*)
Lemma wfcom_rel_downc: forall P x,
  wfcom_rel P x -> 
    (forall Q, In Q (sub_com P) -> wfcom_rel Q x).
Proof. induction P as [ | | | | | P1 IHP1 P2 IHP2 | z R IHR ]. 
6: (* P = SEQ P1 P2 *) 
  {  unfold wfcom_rel. fold wfcom_rel.
     unfold sub_com. fold sub_com.
     intros x Hand. destruct Hand as (HandL, HandR) .
     intro Q.
     (* Check (in_app_iff (sub_com P1) (sub_com P2) Q). *)
     rewrite (in_app_iff (sub_com P1) (sub_com P2) Q).
     (* In a (l ++ l') <-> In a l \/ In a l' *)
     intro Hor . destruct Hor  as [HorL | HorR ] .
     - apply (IHP1 x HandL Q HorL).
     - apply (IHP2 x HandR Q HorR).            }
6: (* Q = FOR z R *)
   { unfold wfcom_rel. fold wfcom_rel.
     unfold sub_com. fold sub_com. simpl In. 
     intros x HwfRx Q HOr.
     destruct HOr as [HEq | HIn].
     + rewrite <- HEq. assumption.
     + apply (IHR x HwfRx Q HIn).              }       
all: simpl. 
all: contradiction. 
Qed.

(** [wfcom_rel_excludes_wr] says that if a [com]mand [P]
is well-formed w.r.t. a variable name [x], then [P] cannot
write [x].
*)
Lemma wfcom_rel_excludes_wr: forall P x,
  wfcom_rel P x -> ~ (In x (vars_wr P)) .
Proof.
induction P.
6: { unfold wfcom_rel. fold wfcom_rel.
     unfold vars_wr. fold vars_wr. unfold "~".
     intros x Hand HIn. apply in_app_iff in HIn.
     unfold "~" in IHP1. unfold vars_wr in IHP1. 
     fold vars_wr in IHP1.
     unfold wfcom_rel in IHP2. fold wfcom_rel in IHP2.
     unfold "~" in IHP2. unfold vars_wr in IHP2. 
     fold vars_wr in IHP2.
     destruct Hand as (HwfP1, HwfP2).
     destruct HIn as [ HInP1 | HInP2].
     - apply (IHP1 x HwfP1 HInP1).
     - apply (IHP2 x HwfP2 HInP2).                     }
6: { unfold wfcom_rel. fold wfcom_rel.
     unfold vars_wr. fold vars_wr. unfold "~".
     intros z H HIn.
     unfold "~" in IHP.
     apply (IHP z H HIn).
}
- simpl. intros x H HFalse. assumption.
- simpl. intros z HNeq HFalse. 
  destruct HFalse as [HEq | HF ].
  + unfold "<>" in HNeq. apply HNeq. rewrite HEq. reflexivity. 
  + assumption.
- simpl. intros z HNeq HFalse. 
  destruct HFalse as [HEq | HF ].
  + unfold "<>" in HNeq. apply HNeq. rewrite HEq. reflexivity.
  + assumption.
- simpl. intros z HNeq HFalse. 
  destruct HFalse as [HEq | HF ].
  + unfold "<>" in HNeq. apply HNeq. rewrite HEq. reflexivity. 
  + assumption.
- simpl. intros z HNeq HFalse. 
  destruct HFalse as [HEq | HF ].
  + unfold "<>" in HNeq. apply HNeq. rewrite HEq. reflexivity. 
  + assumption.
Qed.

(** [wfcom] is down-ward closed, namely i a [com]mand [P] is
sell-formed, all its sub-[com]mmand are.
*)
Lemma wfcom_downc: forall P,
  wfcom P -> (forall Q, In Q (sub_com P) -> wfcom Q).
Proof. induction P as [ | | | | | P1 IHP1 P2 IHP2 | x R IHR ]. 
6: (* P = SEQ P1 P2 *) 
  {  unfold wfcom. fold wfcom.
     unfold sub_com. fold sub_com.
     intro Hand. destruct Hand as (HandL, HandR) .
     intro Q.
     (* Check (in_app_iff (sub_com P1) (sub_com P2) Q). *)
     rewrite (in_app_iff (sub_com P1) (sub_com P2) Q).
     (* In a (l ++ l') <-> In a l \/ In a l' *)
     intro Hor . destruct Hor  as [HorL | HorR ] .
     - apply (IHP1 HandL Q HorL).
     - apply (IHP2 HandR Q HorR).            }
6: (* Q = FOR x R *)
   { unfold wfcom. fold wfcom.
     unfold sub_com. fold sub_com.
     intros H Q. 
     destruct H as (HwfR, HxNotInR).
     (* Search (In _ (_ :: _ )). *)
     intro HQInR. simpl In in HQInR. 
     destruct HQInR as [HReqQ | HQInR].
     + rewrite <- HReqQ. assumption.
     + apply (IHR HwfR Q HQInR  ).          }       
all: intro Q.  
all: simpl.
all: contradiction. 
Qed.

(** "Weaker" statement about the down-ward closure of a 
[com]mand.
*)
Lemma wfcom_downc_weaker: forall P Q,
  wfcom P -> In Q (sub_com P) -> wfcom Q.
Proof. induction P as [ | | | | | P1 IHP1 P2 IHP2 | x R IHR ]. 
6: { 
  intro Q. 
  unfold wfcom. fold wfcom.
  unfold sub_com. fold sub_com.
  rewrite (in_app_iff (sub_com P1) (sub_com P2) Q).
  intro Hand. destruct Hand as (HandL, HandR) .
  intro Hor . destruct Hor  as [HorL | HorR ] .
    - apply (IHP1 Q HandL HorL).
    - apply (IHP2 Q HandR HorR).  
}
6: { 
  intro Q. 
  unfold wfcom. fold wfcom.
  unfold sub_com. fold sub_com.
  intros H HQInR. simpl In in HQInR. 
  destruct H as (HwfR, HxNotInR).
  destruct HQInR as [HReqQ | HQInR].
  + rewrite <- HReqQ. assumption.
  + apply (IHR Q HwfR HQInR).            
}
all: intro Q. 
all: simpl.  
all: contradiction. 
Qed.


(** [inv]ersion preserves the list of [ident]ifiers.
Very likely it preserves also the writable [ident]ifiers,
but the proof is currenlty missing.
*)
Lemma inv_vars_eq: forall x P, 
  In x (vars (inv P)) <-> In x (vars P).
Proof. induction P.
6: { unfold inv. fold inv. unfold vars. fold vars. 
     rewrite in_app_iff. rewrite in_app_iff. 
     split.
     + intro Hor. destruct Hor.
       * right. rewrite <- IHP2. assumption.  
       * left. rewrite <- IHP1. assumption.
     + intro Hor. destruct Hor.
       * right. rewrite IHP1. assumption.  
       * left. rewrite IHP2. assumption. }
6: { unfold inv. fold inv. unfold vars. fold vars.
     simpl. rewrite IHP. reflexivity. }
all: simpl.
all: reflexivity.
Qed.

Lemma vars_wr_subseteq_vars: forall P,
  (forall x, In x (vars_wr P) -> In x (vars P)).
Proof.
induction P.
1: intros. 
1: tauto.
1,2,3,4: intros; 
         simpl; 
         left;
         simpl in H;
         destruct H;
         try assumption;
         try contradiction. 
+ intros.
  simpl in *.
  rewrite in_app_iff in *.
  destruct H.
  * left.  exact (IHP1 x H).
  * right. exact (IHP2 x H).
+ intros.
  simpl in *.
  right.
  exact (IHP x0 H).
Qed.

Lemma vars_wr_subseteq_vars_contra: forall P,
  (forall x, not (In x (vars P)) -> not (In x (vars_wr P)) ).
Proof.
intros. 
intro.
assert (In x (vars P)).
exact (vars_wr_subseteq_vars P x H0).
contradiction.
Qed.

Lemma inv_vars_wr_eq: forall x P, 
  In x (vars_wr (inv P)) <-> In x (vars_wr P).
Proof. 
induction P.
1-5: simpl; reflexivity.
all: unfold inv; fold inv.
all: unfold vars_wr; fold vars_wr.
+ repeat rewrite in_app_iff.
  split.
  * intro Hor. destruct Hor.
    - right. rewrite <- IHP2. assumption.
    - left.  rewrite <- IHP1. assumption.
  * intro Hor. destruct Hor.
    - right. rewrite IHP1. assumption.
    - left.  rewrite IHP2. assumption.
+ exact IHP.
Qed.

(** [inv]ersion preserves well-formedness.
Very likely, it preserves the relative well-formedness
[wfcom_rel], but the proof is currently missibng.
*)
Lemma wfcom_inv: forall P,
  wfcom P <-> wfcom (inv P).
Proof. induction P as [ | | | | | P1 IHP1 P2 IHP2 | x R IHR ].
1-5: simpl; tauto.
+ rewrite inv_unfold_SEQ. unfold wfcom. fold wfcom.
  rewrite IHP1. rewrite IHP2.
  tauto.
+ rewrite inv_unfold_FOR. 
  unfold wfcom. fold wfcom.
  rewrite IHR.
  rewrite inv_vars_wr_eq.
  tauto.
Qed.

Lemma wfcom_rel_inv: forall P x,
  wfcom_rel P x <-> wfcom_rel (inv P) x.
Proof. induction P as [ | | | | | P1 IHP1 P2 IHP2 | x R IHR ].
1-5: simpl; tauto.
+ intro.
  rewrite inv_unfold_SEQ. unfold wfcom_rel. fold wfcom_rel.
  rewrite IHP1. rewrite IHP2.
  tauto.
+ intro.
  rewrite inv_unfold_FOR. 
  unfold wfcom_rel. fold wfcom_rel.
  rewrite (IHR x0).
  tauto.
Qed.