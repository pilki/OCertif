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

Lemma iter_spec :forall A,
  Spec iter f l |R>> forall (I:list A->hprop),
    (forall x t, (App f x;) (I (x::t)) (# I t)) -> 
    R (I l) (# I nil).
Proof.
  intro A.
  xintros.
  intros f l I PRE.
  apply app_spec_2.

  induction l.

  xcf. intros. subst.
  xmatch. xret. auto.

  xcf. intros; subst. xmatch.
  xseq; eauto. xapp*. auto.
Qed.

Lemma length_aux_spec: forall A,
  Spec length_aux (len: int) (l: list A) |R>>
    keep R [] (\= ((Datatypes.length l) + len)).
Proof.
  intro. xintros.
  intros len l.
  apply app_spec_2. revert len.
  induction l;intro len; xcf; intros; subst.

  xgo.

  xgo. reflexivity. reflexivity.
  simpl.
  replace (S(Datatypes.length l) + len) with (Datatypes.length l + (len + 1)).
  eauto. math.
Qed.

Hint Extern 1 (RegisterSpec length_aux) => Provide length_aux_spec.


Lemma length_spec: forall A,
  Spec length (l: list A) |R>>
    keep R [] (\= my_Z_of_nat (Datatypes.length l)).
Proof.
  intro A. xcf.
  intro l.
  xapp. rewrite Zplus_0_r.
  eauto.
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
  xintros. intros l n SUP INF.
(*  remember (abs n) as m.
  replace n with (Z_of_nat m) in * by (subst; apply abs_pos; auto).
  clear dependent n.
  assert (m < Datatypes.length l). math. clear INF. clear Heqm.*)

  apply app_spec_2. xcf. intros; subst.
  xif. math.

  clear C.
  xlet
    (fun nth_aux => Spec nth_aux (l':list A) (n':int) |R>>
      (0 <=n') -> (n' < List.length l') ->
      R [] (fun res=> [List.nth_error l' (Zabs_nat n') = Some res])).
  intros.
  xintros. skip.
  intros l' n' SUP' INF'.
  remember (abs n') as m'.
  replace n' with (Z_of_nat m') in * by (subst; apply abs_pos; auto).
  clear dependent n'.
  assert (m' < Datatypes.length l'). math. clear INF'. clear Heqm'.
  apply app_spec_2.
  revert dependent m'. induction l'; intros.
Admitted.



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






