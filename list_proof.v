Set Implicit Arguments.

Require Import LibCore CFLib  LibList.

Require Import list_ml.
Open Scope comp_scope.


Lemma iter_spec1 :forall A,
  Spec iter f l |R>> forall (l': list A) (I:list A->hprop),
    (forall x t, (App f x;) (I (x::t)) (# I t)) -> 
    R ([l=l'] \* I l') (# [l=l'] \* I nil).
Proof.
  intro A.
  xinduct (unproj31 func (list A) (@list_sub A)).
  xcf. intros * IH * PRE.
  hclean. intro. subst.
  xmatch.
    xret.
    hcancel. assumption.
  xseq. eapply PRE.
  xapp; eauto.
    hcancel.
    hcancel. hcancel.
    reflexivity.
Qed.

Ltac xinduction_noheap_base_lt lt ::=
  first   
    [ eapply (spec_induction_1_noheap (lt:=lt))
    | eapply (spec_induction_2_noheap (lt:=lt))
    | eapply (spec_induction_3_noheap (lt:=lt)) 
    | eapply (spec_induction_4_noheap (lt:=lt)) 
    | eapply (spec_induction_2_noheap (lt:=uncurryp2 lt))
    | eapply (spec_induction_3_noheap (lt:=uncurryp3 lt))
    | eapply (spec_induction_4_noheap (lt:=uncurryp4 lt)) ];
  [ try prove_wf | try xisspec |unfolds_wf ].

Lemma iter_spec :forall A,
  Spec iter f l |R>> forall (I:list A->hprop),
    (forall x t, (App f x;) (I (x::t)) (# I t)) ->
    R (I l) (# I nil).
Proof.
  intro A.
  xinduction (unproj22 func (@list_sub A)).
  xcf. intros f l IH * Sf.
  xgo; auto. hsimpl.
Qed.

Lemma length_aux_spec: forall A,
  Spec length_aux (len: int) (l: list A) |R>>
    keep R [] (\= ((Datatypes.length l) + len)).
Proof.
(*  intro. xintros.
  intros len l. revert len.
  induction_wf: (@list_sub_wf A) l.
  intro. xcf_app.
  xgo.
  xapply IH. auto. hsimpl. hsimpl. simpl. math.*)

  intro A. xinduction (unproj22 int (@list_sub A)).
  xcf. intros.
  xmatch. xret. xapp. auto.
  hsimpl. simpl. math.
Qed.

Hint Extern 1 (RegisterSpec length_aux) => Provide length_aux_spec.



Lemma length_spec: forall A,
  Spec length (l: list A) |R>>
    keep R [] (\= (Datatypes.length l:int)).
Proof.
  intro A. xcf.
  intro l.
  xapp.
  hsimpl. math.
Qed.


Hint Extern 1 (RegisterSpec length) => Provide length_spec.

Lemma hd_spec:forall X, Spec hd l |R>> forall (h:X) (t: list X),
  keep R ([l = (h::t)]) (\= h).
Proof.
  xcf. intros. hclean. intro. subst.
  xmatch.
  xrets; reflexivity.
Qed.

Lemma tl_spec: forall X, Spec tl l |R>> forall (h:X) (t: list X),
  keep R ([l = (h::t)]) (\= t).
Proof.
  xcf. intros. hclean. intro. subst.
  xmatch.
  xrets; reflexivity.
Qed.

Hint Extern 1 (RegisterSpec hd) => Provide hd_spec.
Hint Extern 1 (RegisterSpec tl) => Provide tl_spec.


Lemma nth_spec: forall A,
  Spec nth (l: list A) (n: int) |R>> (0 <=n) -> (n < List.length l) ->
    R [] (fun res=> [List.nth_error l (Zabs_nat n) = Some res]).
Proof.
  intro A.
  xcf. intros * POS INF.
  xif. xfail. math.

(*  xfun_noxbody (fun f => Spec f (l: list A) (n: int) |R>> (0 <=n) -> (n < List.length l) ->
    R [] (fun res=> [List.nth_error l (Zabs_nat n) = Some res])).

  xinduction (unproj21 int (@list_sub A)).
  xbody.*)
  xfun_induction (fun f => Spec f (l: list A) (n: int) |R>> (0 <=n) -> (n < List.length l) ->
    R [] (fun res=> [List.nth_error l (Zabs_nat n) = Some res])) (unproj21 int (@list_sub A)).
  intros SPEC POS' INF'.
  Tactic Notation "xval" :=
    apply local_erase; intro; let x := get_last_hyp tt in revert x; xval as x.

  Tactic Notation "xvals" :=
    apply local_erase; intro; intro_subst.

  xvals.
  xmatch. xfail. simpl in INF'. math.

  xif. xret. hsimpl. change (abs 0) with O. simpl. reflexivity.

  xapp; auto. math.  simpl in *. math. hsimpl.
  math_rewrite (n0 = 1 + (n0 -1)).
  replace (abs (1 + (n0 -1))) with (S (abs (n0 - 1))). simpl. auto.
  zify. subst. intuition.

  xgo*.
Qed.



Lemma append_spec: forall A,
  Spec append' (l1: list A) (l2: list A) |R>>
    keep R [] (\= (app l1 l2)).
Proof.
  intro a. xintros. intros l1 l2.
  apply app_spec_2.
  induction l1; xcf; intros; subst.

  xgo.

  xgo; auto.
  hextract. subst. simpl. hcancel. reflexivity.
Qed.

Hint Extern 1 (RegisterSpec append') => Provide append_spec.

Lemma rev_append_spec: forall A,
  Spec rev_append' (l1: list A) (l2: list A) |R>>
    keep R [] (\= (List.rev_append l1 l2)).
Proof.
  intro a. xintros. intros l1 l2.
  apply app_spec_2. revert l2.
  induction l1; intro; xcf; intros; subst.

  xgo.

  xgo; auto.
Qed.

Hint Extern 1 (RegisterSpec rev_append') => Provide rev_append_spec.


Lemma rev_spec': forall A,
  Spec rev (l: list A) |R>>
    keep R [] (\= (List.rev' l)).
Proof.
  intro A.
  xcf. intro l.
  unfold rev'. xgo.
  hextract. subst.
  hcancel. reflexivity.
Qed.

Lemma rev_spec: forall A,
  Spec rev (l: list A) |R>>
    keep R [] (\= (List.rev l)).
Proof.
  intro. xintros. intro l. rewrite rev_alt.
  xgo.
  hextract. subst.
  hcancel. reflexivity.
Qed.

Hint Extern 1 (RegisterSpec rev) => Provide rev_spec.






