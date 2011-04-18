Set Implicit Arguments.

Require Import CFPrim.

Notation
"''_m1'" := (`0) (at level 0) : atom_scope.

Notation
"''_x5'" := (`1`0) (at level 0) : atom_scope.

Notation
"''nth_aux'" := (`2`0) (at level 0) : atom_scope.

Notation
"''_x3'" := (`1`1`0) (at level 0) : atom_scope.

Notation
"''_x4'" := (`1`2`0) (at level 0) : atom_scope.

Notation
"''_x6'" := (`2`1`0) (at level 0) : atom_scope.

Notation
"''r'" := (`2`2`0) (at level 0) : atom_scope.

Notation
"''rmap_f'" := (`1`1`1`0) (at level 0) : atom_scope.

Notation
"''_x1'" := (`1`1`2`0) (at level 0) : atom_scope.

Notation
"''_x9'" := (`1`2`1`0) (at level 0) : atom_scope.

Notation
"''_x7'" := (`1`2`2`0) (at level 0) : atom_scope.

Notation
"''rmap2_f'" := (`2`1`1`0) (at level 0) : atom_scope.

Notation
"''_x2'" := (`2`1`2`0) (at level 0) : atom_scope.

Notation
"''find'" := (`2`2`1`0) (at level 0) : atom_scope.

Notation
"''_m2'" := (`2`2`2`0) (at level 0) : atom_scope.

Notation
"''_x8'" := (`1`1`1`1`0) (at level 0) : atom_scope.

Notation
"''_x13'" := (`1`1`1`2`0) (at level 0) : atom_scope.

Notation
"''_x20'" := (`1`1`2`1`0) (at level 0) : atom_scope.

Global
Instance length_aux_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter length_aux : CFSpec.func.

Parameter
length_aux_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : (int ->
((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall len
: int, (forall _x0 : (list _A), (((K len) _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
len)))))) H) Q))) ((Logic.not ((Logic.eq _x0) Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _A, (forall l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_apply _ _ ((((((@app_2
int) (list _A)) int) length_aux) ((Coq.ZArith.BinInt.Zplus
len) (1)%Z)) l)) H) Q))))) ((forall a : _A, (forall
l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) length_aux))))))).

Hint Extern 1 (RegisterCf length_aux)
=> Provide length_aux_cf.

Global Instance length_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
length : CFSpec.func.

Parameter length_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : ((list _A) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)), ((is_spec_1
K) -> ((forall l : (list _A), ((K l) (@CFPrint.tag
tag_apply _ _ ((((((@app_2 int) (list _A)) int) length_aux)
(0)%Z) l)))) -> ((spec_1 K) length))))))).

Hint Extern
1 (RegisterCf length) => Provide length_cf.

Global
Instance hd_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter hd : CFSpec.func.

Parameter
hd_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : ((list
_A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) ->
Prop)) -> Prop)), ((is_spec_1 K) -> ((forall _x0 :
(list _A), ((K _x0) (@CFPrint.tag (tag_match 2%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x0) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_fail
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => False)))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_ret _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
((pred_le H) (Q a)))))) H) Q))))) ((forall a : _A,
(forall l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))))) -> ((spec_1
K) hd))))))).

Hint Extern 1 (RegisterCf hd) => Provide
hd_cf.

Global Instance tl_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter tl : CFSpec.func.

Parameter
tl_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : ((list
_A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) ->
Prop)) -> Prop)), ((is_spec_1 K) -> ((forall _x0 :
(list _A), ((K _x0) (@CFPrint.tag (tag_match 2%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x0) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_fail
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => False)))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_ret _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
((pred_le H) (Q l)))))) H) Q))))) ((forall a : _A,
(forall l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))))) -> ((spec_1
K) tl))))))).

Hint Extern 1 (RegisterCf tl) => Provide
tl_cf.

Global Instance nth_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter nth : CFSpec.func.

Parameter
nth_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : ((list
_A) -> (int -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall l
: (list _A), (forall n : int, (((K l) n) (@CFPrint.tag
tag_if _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq (((fun
_y _z => istrue (_y < _z)) n) (0)%Z)) true) -> (((@CFPrint.tag
tag_fail _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => False)))) H) Q))) (((Logic.eq
(((fun _y _z => istrue (_y < _z)) n) (0)%Z)) false)
-> (((@CFPrint.tag tag_let_fun (Label_create 'nth_aux)
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall nth_aux : CFSpec.func, (Logic.ex (fun Pnth_aux
: (CFSpec.func -> Prop) => ((Logic.and ((@CFPrint.tag
tag_body _ _ (forall _B : Type, (forall K : ((list
_B) -> (int -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall l
: (list _B), (forall n : int, (((K l) n) (@CFPrint.tag
tag_let_val _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => (forall _x5 : (list _B),
(((Logic.eq _x5) l) -> (((@CFPrint.tag (tag_match 2%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x5) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_fail
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => False)))) H) Q))) ((Logic.not ((Logic.eq
_x5) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _B, (forall
l : (list _B), (((Logic.eq _x5) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_if _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
((Logic.and (((Logic.eq (((fun _y _z => istrue (_y
= _z)) n) (0)%Z)) true) -> (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q a)))))) H) Q))) (((Logic.eq
(((fun _y _z => istrue (_y = _z)) n) (0)%Z)) false)
-> (((@CFPrint.tag tag_apply _ _ ((((((@app_2 (list
_B)) int) _B) nth_aux) l) ((Coq.ZArith.BinInt.Zminus
n) (1)%Z))) H) Q))))))) H) Q))))) ((forall a : _B,
(forall l : (list _B), (Logic.not ((Logic.eq _x5) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))) H) Q))))))))))
-> ((spec_2 K) nth_aux)))))) -> (Pnth_aux nth_aux)))
((Pnth_aux nth_aux) -> (((@CFPrint.tag tag_apply _
_ ((((((@app_2 (list _A)) int) _A) nth_aux) l) n))
H) Q)))))))))) H) Q)))))))))) -> ((spec_2 K) nth))))))).

Hint
Extern 1 (RegisterCf nth) => Provide nth_cf.

Global
Instance append'_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter append' : CFSpec.func.

Parameter
append'_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : ((list
_A) -> ((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall l1
: (list _A), (forall l2 : (list _A), (((K l1) l2) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq l1) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
l2)))))) H) Q))) ((Logic.not ((Logic.eq l1) Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
hd : _A, (forall tl : (list _A), (((Logic.eq l1) ((Coq.Lists.List.cons
hd) tl)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x3) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : ((list _A)
-> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag tag_apply
_ _ ((((((@app_2 (list _A)) (list _A)) (list _A)) append')
tl) l2)) H) Q1)) (forall _x3 : (list _A), (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q ((Coq.Lists.List.cons
hd) _x3))))))) (Q1 _x3)) Q))))))))) H) Q))))) ((forall
hd : _A, (forall tl : (list _A), (Logic.not ((Logic.eq
l1) ((Coq.Lists.List.cons hd) tl))))) -> (((@CFPrint.tag
tag_done _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => True)))) H) Q))))))) H)
Q))))))))))) -> ((spec_2 K) append'))))))).

Hint Extern
1 (RegisterCf append') => Provide append'_cf.

Global
Instance rev_append'_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter rev_append' : CFSpec.func.

Parameter
rev_append'_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : ((list
_A) -> ((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall l1
: (list _A), (forall l2 : (list _A), (((K l1) l2) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq l1) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
l2)))))) H) Q))) ((Logic.not ((Logic.eq l1) Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _A, (forall l : (list _A), (((Logic.eq l1) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_apply _ _ ((((((@app_2
(list _A)) (list _A)) (list _A)) rev_append') l) ((Coq.Lists.List.cons
a) l2))) H) Q))))) ((forall a : _A, (forall l : (list
_A), (Logic.not ((Logic.eq l1) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) rev_append'))))))).

Hint Extern 1 (RegisterCf rev_append')
=> Provide rev_append'_cf.

Global Instance rev_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
rev : CFSpec.func.

Parameter rev_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : ((list _A) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)), ((is_spec_1
K) -> ((forall l : (list _A), ((K l) (@CFPrint.tag
tag_apply _ _ ((((((@app_2 (list _A)) (list _A)) (list
_A)) rev_append') l) Coq.Lists.List.nil)))) -> ((spec_1
K) rev))))))).

Hint Extern 1 (RegisterCf rev) => Provide
rev_cf.

Global Instance flatten_type_inhab : (Inhab
CFSpec.func).

Proof. inhab. Qed.



Parameter flatten
: CFSpec.func.

Parameter flatten_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : ((list (list _A)) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)), ((is_spec_1
K) -> ((forall _x0 : (list (list _A)), ((K _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
Coq.Lists.List.nil)))))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall l : (list _A),
(forall r : (list (list _A)), (((Logic.eq _x0) ((Coq.Lists.List.cons
l) r)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x4) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : ((list _A)
-> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag tag_apply
_ _ ((((@app_1 (list (list _A))) (list _A)) flatten)
r)) H) Q1)) (forall _x4 : (list _A), (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 (list _A)) (list _A)) (list
_A)) append') l) _x4)) (Q1 _x4)) Q))))))))) H) Q)))))
((forall l : (list _A), (forall r : (list (list _A)),
(Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons l)
r))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))))) -> ((spec_1
K) flatten))))))).

Hint Extern 1 (RegisterCf flatten)
=> Provide flatten_cf.

Global Instance concat_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
concat : CFSpec.func.

Parameter concat_cf : (@CFPrint.tag
tag_top_val _ _ (forall _A : Type, ((Logic.eq concat)
flatten))).

Hint Extern 1 (RegisterCf concat) => Provide
concat_cf.

Global Instance map_type_inhab : (Inhab
CFSpec.func).

Proof. inhab. Qed.



Parameter map
: CFSpec.func.

Parameter map_cf : (@CFPrint.tag tag_top_fun
_ _ (@CFPrint.tag tag_body _ _ (forall _B : Type, (forall
_A : Type, (forall K : (CFSpec.func -> ((list _A) ->
((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop))), ((is_spec_2 K) -> ((forall f : CFSpec.func,
(forall _x0 : (list _A), (((K f) _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
Coq.Lists.List.nil)))))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'r) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (_B -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((@app_1
_A) _B) f) a)) H) Q1)) (forall r : _B, (((@CFPrint.tag
tag_let_trm (Label_create '_x6) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : ((list _B) -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 CFSpec.func) (list _A))
(list _B)) map) f) l)) H) Q1)) (forall _x6 : (list
_B), (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
((Coq.Lists.List.cons r) _x6))))))) (Q1 _x6)) Q)))))))))
(Q1 r)) Q))))))))) H) Q))))) ((forall a : _A, (forall
l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) map)))))))).

Hint Extern 1 (RegisterCf map) =>
Provide map_cf.

Global Instance rev_map_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
rev_map : CFSpec.func.

Parameter rev_map_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_B : Type, (forall _A : Type, (forall K : (CFSpec.func
-> ((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall f
: CFSpec.func, (forall l : (list _A), (((K f) l) (@CFPrint.tag
tag_let_fun (Label_create 'rmap_f) _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
(forall rmap_f : CFSpec.func, (Logic.ex (fun Prmap_f
: (CFSpec.func -> Prop) => ((Logic.and ((@CFPrint.tag
tag_body _ _ (forall K : ((list _B) -> ((list _A) ->
((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop))), ((is_spec_2 K) -> ((forall accu : (list
_B), (forall _x0 : (list _A), (((K accu) _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
accu)))))) H) Q))) ((Logic.not ((Logic.eq _x0) Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _A, (forall l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x5) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (_B -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((@app_1
_A) _B) f) a)) H) Q1)) (forall _x5 : _B, (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 (list _B)) (list _A)) (list
_B)) rmap_f) ((Coq.Lists.List.cons _x5) accu)) l))
(Q1 _x5)) Q))))))))) H) Q))))) ((forall a : _A, (forall
l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) rmap_f))))) -> (Prmap_f rmap_f))) ((Prmap_f rmap_f)
-> (((@CFPrint.tag tag_apply _ _ ((((((@app_2 (list
_B)) (list _A)) (list _B)) rmap_f) Coq.Lists.List.nil)
l)) H) Q))))))))))))) -> ((spec_2 K) rev_map)))))))).

Hint
Extern 1 (RegisterCf rev_map) => Provide rev_map_cf.

Global
Instance iter_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter iter : CFSpec.func.

Parameter
iter_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : (CFSpec.func
-> ((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall f
: CFSpec.func, (forall _x0 : (list _A), (((K f) _x0)
(@CFPrint.tag (tag_match 2%nat) _ _ (@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
Coq.Init.Datatypes.tt)))))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_seq _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
(Logic.ex (fun Q' : (_ -> CFHeaps.hprop) => ((Logic.and
(((@CFPrint.tag tag_apply _ _ ((((@app_1 _A) unit)
f) a)) H) Q')) (((@CFPrint.tag tag_apply _ _ ((((((@app_2
CFSpec.func) (list _A)) unit) iter) f) l)) (Q' tt))
Q)))))))) H) Q))))) ((forall a : _A, (forall l : (list
_A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) iter))))))).

Hint Extern 1 (RegisterCf iter) =>
Provide iter_cf.

Global Instance fold_left_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
fold_left : CFSpec.func.

Parameter fold_left_cf :
(@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag tag_body
_ _ (forall _B : Type, (forall _A : Type, (forall K
: (CFSpec.func -> (_A -> ((list _B) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)))), ((is_spec_3
K) -> ((forall f : CFSpec.func, (forall accu : _A,
(forall l : (list _B), ((((K f) accu) l) (@CFPrint.tag
tag_let_val _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => (forall _x1 : (list _B),
(((Logic.eq _x1) l) -> (((@CFPrint.tag (tag_match 2%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x1) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q accu)))))) H) Q)))
((Logic.not ((Logic.eq _x1) Coq.Lists.List.nil)) ->
(((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _B, (forall l : (list _B), (((Logic.eq _x1) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x4) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (_A -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((((@app_2
_A) _B) _A) f) accu) a)) H) Q1)) (forall _x4 : _A,
(((@CFPrint.tag tag_apply _ _ ((((((((@app_3 CFSpec.func)
_A) (list _B)) _A) fold_left) f) _x4) l)) (Q1 _x4))
Q))))))))) H) Q))))) ((forall a : _B, (forall l : (list
_B), (Logic.not ((Logic.eq _x1) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))) H) Q)))))))))))
-> ((spec_3 K) fold_left)))))))).

Hint Extern 1 (RegisterCf
fold_left) => Provide fold_left_cf.

Global Instance
fold_right_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter fold_right : CFSpec.func.

Parameter
fold_right_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _B : Type, (forall _A : Type,
(forall K : (CFSpec.func -> ((list _A) -> (_B -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)))), ((is_spec_3
K) -> ((forall f : CFSpec.func, (forall l : (list _A),
(forall accu : _B, ((((K f) l) accu) (@CFPrint.tag
tag_let_val _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => (forall _x1 : (list _A),
(((Logic.eq _x1) l) -> (((@CFPrint.tag (tag_match 2%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x1) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q accu)))))) H) Q)))
((Logic.not ((Logic.eq _x1) Coq.Lists.List.nil)) ->
(((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _A, (forall l : (list _A), (((Logic.eq _x1) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x4) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (_B -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((((((@app_3
CFSpec.func) (list _A)) _B) _B) fold_right) f) l) accu))
H) Q1)) (forall _x4 : _B, (((@CFPrint.tag tag_apply
_ _ ((((((@app_2 _A) _B) _B) f) a) _x4)) (Q1 _x4))
Q))))))))) H) Q))))) ((forall a : _A, (forall l : (list
_A), (Logic.not ((Logic.eq _x1) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q)))))))) H) Q)))))))))))
-> ((spec_3 K) fold_right)))))))).

Hint Extern 1 (RegisterCf
fold_right) => Provide fold_right_cf.

Global Instance
map2_type_inhab : (Inhab CFSpec.func).

Proof. inhab.
Qed.



Parameter map2 : CFSpec.func.

Parameter map2_cf
: (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag tag_body
_ _ (forall _C : Type, (forall _B : Type, (forall _A
: Type, (forall K : (CFSpec.func -> ((list _A) -> ((list
_B) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) ->
Prop)) -> Prop)))), ((is_spec_3 K) -> ((forall f :
CFSpec.func, (forall l1 : (list _A), (forall l2 : (list
_B), ((((K f) l1) l2) (@CFPrint.tag tag_let_val _ _
(local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall _x3 : ((prod (list _A)) (list _B)), (((Logic.eq
_x3) (l1,l2)) -> (((@CFPrint.tag (tag_match 3%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q Coq.Lists.List.nil))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create 'r) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (_C -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 _A) _B) _C) f) a1) a2))
H) Q1)) (forall r : _C, (((@CFPrint.tag tag_let_trm
(Label_create '_x9) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : ((list _C) -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((((@app_3 CFSpec.func) (list _A))
(list _B)) (list _C)) map2) f) l1) l2)) H) Q1)) (forall
_x9 : (list _C), (((@CFPrint.tag tag_ret _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((pred_le H) (Q ((Coq.Lists.List.cons r) _x9)))))))
(Q1 _x9)) Q))))))))) (Q1 r)) Q))))))))) H) Q)))))))
((forall a1 : _A, (forall l1 : (list _A), (forall a2
: _B, (forall l2 : (list _B), (Logic.not ((Logic.eq
_x3) (((Coq.Lists.List.cons a1) l1),((Coq.Lists.List.cons
a2) l2)))))))) -> (((@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (forall _p0 : (list _A), (forall _p1
: (list _B), (((Logic.eq _x3) (_p0,_p1)) -> (((@CFPrint.tag
tag_fail _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => False)))) H) Q))))) ((forall
_p0 : (list _A), (forall _p1 : (list _B), (Logic.not
((Logic.eq _x3) (_p0,_p1))))) -> (((@CFPrint.tag tag_done
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => True)))) H) Q))))))) H) Q)))))))
H) Q)))))))) H) Q))))))))))) -> ((spec_3 K) map2))))))))).

Hint
Extern 1 (RegisterCf map2) => Provide map2_cf.

Global
Instance rev_map2_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter rev_map2 : CFSpec.func.

Parameter
rev_map2_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _C : Type, (forall _B : Type,
(forall _A : Type, (forall K : (CFSpec.func -> ((list
_A) -> ((list _B) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop)))), ((is_spec_3 K) -> ((forall f
: CFSpec.func, (forall l1 : (list _A), (forall l2 :
(list _B), ((((K f) l1) l2) (@CFPrint.tag tag_let_fun
(Label_create 'rmap2_f) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (forall rmap2_f
: CFSpec.func, (Logic.ex (fun Prmap2_f : (CFSpec.func
-> Prop) => ((Logic.and ((@CFPrint.tag tag_body _ _
(forall K : ((list _C) -> ((list _A) -> ((list _B)
-> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop)))), ((is_spec_3 K) -> ((forall accu : (list
_C), (forall l1 : (list _A), (forall l2 : (list _B),
((((K accu) l1) l2) (@CFPrint.tag tag_let_val _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall _x3 : ((prod (list _A)) (list _B)), (((Logic.eq
_x3) (l1,l2)) -> (((@CFPrint.tag (tag_match 3%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q accu))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x7) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (_C -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 _A) _B) _C) f) a1) a2))
H) Q1)) (forall _x7 : _C, (((@CFPrint.tag tag_apply
_ _ ((((((((@app_3 (list _C)) (list _A)) (list _B))
(list _C)) rmap2_f) ((Coq.Lists.List.cons _x7) accu))
l1) l2)) (Q1 _x7)) Q))))))))) H) Q))))))) ((forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2)))))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _A), (forall _p1 : (list _B), (((Logic.eq _x3)
(_p0,_p1)) -> (((@CFPrint.tag tag_fail _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> False)))) H) Q))))) ((forall _p0 : (list _A), (forall
_p1 : (list _B), (Logic.not ((Logic.eq _x3) (_p0,_p1)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))) H) Q)))))))) H) Q))))))))))) -> ((spec_3
K) rmap2_f))))) -> (Prmap2_f rmap2_f))) ((Prmap2_f
rmap2_f) -> (((@CFPrint.tag tag_apply _ _ ((((((((@app_3
(list _C)) (list _A)) (list _B)) (list _C)) rmap2_f)
Coq.Lists.List.nil) l1) l2)) H) Q)))))))))))))) ->
((spec_3 K) rev_map2))))))))).

Hint Extern 1 (RegisterCf
rev_map2) => Provide rev_map2_cf.

Global Instance
iter2_type_inhab : (Inhab CFSpec.func).

Proof. inhab.
Qed.



Parameter iter2 : CFSpec.func.

Parameter iter2_cf
: (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag tag_body
_ _ (forall _B : Type, (forall _A : Type, (forall K
: (CFSpec.func -> ((list _A) -> ((list _B) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)))), ((is_spec_3
K) -> ((forall f : CFSpec.func, (forall l1 : (list
_A), (forall l2 : (list _B), ((((K f) l1) l2) (@CFPrint.tag
tag_let_val _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => (forall _x3 : ((prod (list
_A)) (list _B)), (((Logic.eq _x3) (l1,l2)) -> (((@CFPrint.tag
(tag_match 3%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
Coq.Init.Datatypes.tt)))))) H) Q))) ((Logic.not ((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall a1
: _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_seq _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => (Logic.ex (fun Q' : (_ ->
CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag tag_apply
_ _ ((((((@app_2 _A) _B) unit) f) a1) a2)) H) Q'))
(((@CFPrint.tag tag_apply _ _ ((((((((@app_3 CFSpec.func)
(list _A)) (list _B)) unit) iter2) f) l1) l2)) (Q'
tt)) Q)))))))) H) Q))))))) ((forall a1 : _A, (forall
l1 : (list _A), (forall a2 : _B, (forall l2 : (list
_B), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2)))))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _A), (forall _p1 : (list _B), (((Logic.eq _x3)
(_p0,_p1)) -> (((@CFPrint.tag tag_fail _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> False)))) H) Q))))) ((forall _p0 : (list _A), (forall
_p1 : (list _B), (Logic.not ((Logic.eq _x3) (_p0,_p1)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))) H) Q)))))))) H) Q))))))))))) -> ((spec_3
K) iter2)))))))).

Hint Extern 1 (RegisterCf iter2)
=> Provide iter2_cf.

Global Instance fold_left2_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
fold_left2 : CFSpec.func.

Parameter fold_left2_cf
: (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag tag_body
_ _ (forall _C : Type, (forall _B : Type, (forall _A
: Type, (forall K : (CFSpec.func -> (_A -> ((list _B)
-> ((list _C) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))))), ((is_spec_4 K) -> ((forall
f : CFSpec.func, (forall accu : _A, (forall l1 : (list
_B), (forall l2 : (list _C), (((((K f) accu) l1) l2)
(@CFPrint.tag tag_let_val _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (forall _x3 : ((prod
(list _B)) (list _C)), (((Logic.eq _x3) (l1,l2)) ->
(((@CFPrint.tag (tag_match 3%nat) _ _ (@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q accu))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _B, (forall l1 : (list _B), (forall a2 : _C, (forall
l2 : (list _C), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x6) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (_A -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((((@app_3 _A) _B) _C) _A) f) accu)
a1) a2)) H) Q1)) (forall _x6 : _A, (((@CFPrint.tag
tag_apply _ _ ((((((((((@app_4 CFSpec.func) _A) (list
_B)) (list _C)) _A) fold_left2) f) _x6) l1) l2)) (Q1
_x6)) Q))))))))) H) Q))))))) ((forall a1 : _B, (forall
l1 : (list _B), (forall a2 : _C, (forall l2 : (list
_C), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2)))))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _B), (forall _p1 : (list _C), (((Logic.eq _x3)
(_p0,_p1)) -> (((@CFPrint.tag tag_fail _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> False)))) H) Q))))) ((forall _p0 : (list _B), (forall
_p1 : (list _C), (Logic.not ((Logic.eq _x3) (_p0,_p1)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))) H) Q)))))))) H) Q)))))))))))) -> ((spec_4
K) fold_left2))))))))).

Hint Extern 1 (RegisterCf
fold_left2) => Provide fold_left2_cf.

Global Instance
fold_right2_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter fold_right2 : CFSpec.func.

Parameter
fold_right2_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _C : Type, (forall _B : Type,
(forall _A : Type, (forall K : (CFSpec.func -> ((list
_A) -> ((list _B) -> (_C -> ((CFHeaps.hprop -> ((_
-> CFHeaps.hprop) -> Prop)) -> Prop))))), ((is_spec_4
K) -> ((forall f : CFSpec.func, (forall l1 : (list
_A), (forall l2 : (list _B), (forall accu : _C, (((((K
f) l1) l2) accu) (@CFPrint.tag tag_let_val _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall _x3 : ((prod (list _A)) (list _B)), (((Logic.eq
_x3) (l1,l2)) -> (((@CFPrint.tag (tag_match 3%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q accu))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x7) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (_C -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((((((@app_4 CFSpec.func) (list _A))
(list _B)) _C) _C) fold_right2) f) l1) l2) accu)) H)
Q1)) (forall _x7 : _C, (((@CFPrint.tag tag_apply _
_ ((((((((@app_3 _A) _B) _C) _C) f) a1) a2) _x7)) (Q1
_x7)) Q))))))))) H) Q))))))) ((forall a1 : _A, (forall
l1 : (list _A), (forall a2 : _B, (forall l2 : (list
_B), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2)))))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _A), (forall _p1 : (list _B), (((Logic.eq _x3)
(_p0,_p1)) -> (((@CFPrint.tag tag_fail _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> False)))) H) Q))))) ((forall _p0 : (list _A), (forall
_p1 : (list _B), (Logic.not ((Logic.eq _x3) (_p0,_p1)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))) H) Q)))))))) H) Q)))))))))))) -> ((spec_4
K) fold_right2))))))))).

Hint Extern 1 (RegisterCf
fold_right2) => Provide fold_right2_cf.

Global Instance
for_all_type_inhab : (Inhab CFSpec.func).

Proof. inhab.
Qed.



Parameter for_all : CFSpec.func.

Parameter
for_all_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : (CFSpec.func
-> ((list _A) -> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop)
-> Prop)) -> Prop))), ((is_spec_2 K) -> ((forall p
: CFSpec.func, (forall _x0 : (list _A), (((K p) _x0)
(@CFPrint.tag (tag_match 2%nat) _ _ (@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
Coq.Init.Datatypes.true)))))) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall a : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x3) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (bool -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((@app_1
_A) bool) p) a)) H) Q1)) (forall _x3 : bool, (((@CFPrint.tag
tag_let_trm (Label_create '_x6) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (bool -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 CFSpec.func) (list _A))
bool) for_all) p) l)) H) Q1)) (forall _x6 : bool, (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q ((LibBool.and
_x3) _x6))))))) (Q1 _x6)) Q))))))))) (Q1 _x3)) Q)))))))))
H) Q))))) ((forall a : _A, (forall l : (list _A), (Logic.not
((Logic.eq _x0) ((Coq.Lists.List.cons a) l))))) ->
(((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))))))) -> ((spec_2 K) for_all))))))).

Hint
Extern 1 (RegisterCf for_all) => Provide for_all_cf.

Global
Instance for_all2_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter for_all2 : CFSpec.func.

Parameter
for_all2_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _B : Type, (forall _A : Type,
(forall K : (CFSpec.func -> ((list _A) -> ((list _B)
-> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop)))), ((is_spec_3 K) -> ((forall p : CFSpec.func,
(forall l1 : (list _A), (forall l2 : (list _B), ((((K
p) l1) l2) (@CFPrint.tag tag_let_val _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall _x3 : ((prod (list _A)) (list _B)), (((Logic.eq
_x3) (l1,l2)) -> (((@CFPrint.tag (tag_match 3%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q Coq.Init.Datatypes.true))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x5) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (bool -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 _A) _B) bool) p) a1) a2))
H) Q1)) (forall _x5 : bool, (((@CFPrint.tag tag_let_trm
(Label_create '_x9) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (bool -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((((@app_3 CFSpec.func) (list _A))
(list _B)) bool) for_all2) p) l1) l2)) H) Q1)) (forall
_x9 : bool, (((@CFPrint.tag tag_ret _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((pred_le H) (Q ((LibBool.and _x5) _x9))))))) (Q1
_x9)) Q))))))))) (Q1 _x5)) Q))))))))) H) Q))))))) ((forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2)))))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _A), (forall _p1 : (list _B), (((Logic.eq _x3)
(_p0,_p1)) -> (((@CFPrint.tag tag_fail _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> False)))) H) Q))))) ((forall _p0 : (list _A), (forall
_p1 : (list _B), (Logic.not ((Logic.eq _x3) (_p0,_p1)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))) H) Q)))))))) H) Q))))))))))) -> ((spec_3
K) for_all2)))))))).

Hint Extern 1 (RegisterCf for_all2)
=> Provide for_all2_cf.

Global Instance memq_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
memq : CFSpec.func.

Parameter memq_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : (_A -> ((list _A) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop))), ((is_spec_2
K) -> ((forall x : _A, (forall _x0 : (list _A), (((K
x) _x0) (@CFPrint.tag (tag_match 2%nat) _ _ (@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x0) Coq.Lists.List.nil) -> (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q Coq.Init.Datatypes.false))))))
H) Q))) ((Logic.not ((Logic.eq _x0) Coq.Lists.List.nil))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a : _A, (forall l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
a) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x3) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (bool -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((((@app_2
_A) _A) bool) ml_phy_eq) a) x)) H) Q1)) (forall _x3
: bool, (((@CFPrint.tag tag_let_trm (Label_create '_x7)
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (Logic.ex (fun Q1 : (bool -> CFHeaps.hprop) => ((Logic.and
(((@CFPrint.tag tag_apply _ _ ((((((@app_2 _A) (list
_A)) bool) memq) x) l)) H) Q1)) (forall _x7 : bool,
(((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
((LibBool.or _x3) _x7))))))) (Q1 _x7)) Q))))))))) (Q1
_x3)) Q))))))))) H) Q))))) ((forall a : _A, (forall
l : (list _A), (Logic.not ((Logic.eq _x0) ((Coq.Lists.List.cons
a) l))))) -> (((@CFPrint.tag tag_done _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> True)))) H) Q))))))) H) Q))))))))))) -> ((spec_2
K) memq))))))).

Hint Extern 1 (RegisterCf memq) =>
Provide memq_cf.

Global Instance find_type_inhab :
(Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
find : CFSpec.func.

Parameter find_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : (CFSpec.func -> ((list _A) ->
((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop))), ((is_spec_2 K) -> ((forall p : CFSpec.func,
(forall _x0 : (list _A), (((K p) _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_fail _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => False)))) H) Q)))
((Logic.not ((Logic.eq _x0) Coq.Lists.List.nil)) ->
(((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
x : _A, (forall l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
x) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x2) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (bool -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((@app_1
_A) bool) p) x)) H) Q1)) (forall _x2 : bool, (((@CFPrint.tag
tag_if _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq _x2)
true) -> (((@CFPrint.tag tag_ret _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
((pred_le H) (Q x)))))) H) Q))) (((Logic.eq _x2) false)
-> (((@CFPrint.tag tag_apply _ _ ((((((@app_2 CFSpec.func)
(list _A)) _A) find) p) l)) H) Q))))))) (Q1 _x2)) Q)))))))))
H) Q))))) ((forall x : _A, (forall l : (list _A), (Logic.not
((Logic.eq _x0) ((Coq.Lists.List.cons x) l))))) ->
(((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))))))) -> ((spec_2 K) find))))))).

Hint Extern
1 (RegisterCf find) => Provide find_cf.

Global Instance
find_all_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter find_all : CFSpec.func.

Parameter
find_all_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : (CFSpec.func
-> ((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop)), ((is_spec_1 K) -> ((forall p : CFSpec.func,
((K p) (@CFPrint.tag tag_let_fun (Label_create 'find)
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall find : CFSpec.func, (Logic.ex (fun Pfind
: (CFSpec.func -> Prop) => ((Logic.and ((@CFPrint.tag
tag_body _ _ (forall K : ((list _A) -> ((list _A) ->
((CFHeaps.hprop -> ((_ -> CFHeaps.hprop) -> Prop))
-> Prop))), ((is_spec_2 K) -> ((forall accu : (list
_A), (forall _x0 : (list _A), (((K accu) _x0) (@CFPrint.tag
(tag_match 2%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_apply _ _ ((((@app_1 (list _A))
(list _A)) rev) accu)) H) Q))) ((Logic.not ((Logic.eq
_x0) Coq.Lists.List.nil)) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall x : _A, (forall
l : (list _A), (((Logic.eq _x0) ((Coq.Lists.List.cons
x) l)) -> (((@CFPrint.tag tag_let_trm (Label_create
'_x4) _ (local (fun H : CFHeaps.hprop => (fun Q : (_
-> CFHeaps.hprop) => (Logic.ex (fun Q1 : (bool -> CFHeaps.hprop)
=> ((Logic.and (((@CFPrint.tag tag_apply _ _ ((((@app_1
_A) bool) p) x)) H) Q1)) (forall _x4 : bool, (((@CFPrint.tag
tag_if _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq _x4)
true) -> (((@CFPrint.tag tag_apply _ _ ((((((@app_2
(list _A)) (list _A)) (list _A)) find) ((Coq.Lists.List.cons
x) accu)) l)) H) Q))) (((Logic.eq _x4) false) -> (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 (list _A)) (list _A)) (list
_A)) find) accu) l)) H) Q))))))) (Q1 _x4)) Q)))))))))
H) Q))))) ((forall x : _A, (forall l : (list _A), (Logic.not
((Logic.eq _x0) ((Coq.Lists.List.cons x) l))))) ->
(((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q))))))))))) -> ((spec_2 K) find))))) -> (Pfind
find))) ((Pfind find) -> (((@CFPrint.tag tag_apply
_ _ ((((@app_1 (list _A)) CFSpec.func) find) Coq.Lists.List.nil))
H) Q)))))))))))) -> ((spec_1 K) find_all))))))).

Hint
Extern 1 (RegisterCf find_all) => Provide find_all_cf.

Global
Instance filter_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter filter : CFSpec.func.

Parameter
filter_cf : (@CFPrint.tag tag_top_val _ _ (forall _A
: Type, ((Logic.eq filter) find_all))).

Hint Extern
1 (RegisterCf filter) => Provide filter_cf.

Global
Instance split_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter split : CFSpec.func.

Parameter
split_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _B : Type, (forall _A : Type,
(forall K : ((list ((prod _A) _B)) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop)), ((is_spec_1
K) -> ((forall _x0 : (list ((prod _A) _B)), ((K _x0)
(@CFPrint.tag (tag_match 2%nat) _ _ (@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (((Logic.eq _x0) Coq.Lists.List.nil)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
(Coq.Lists.List.nil,Coq.Lists.List.nil))))))) H) Q)))
((Logic.not ((Logic.eq _x0) Coq.Lists.List.nil)) ->
(((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
x : _A, (forall y : _B, (forall l : (list ((prod _A)
_B)), (((Logic.eq _x0) ((Coq.Lists.List.cons (x,y))
l)) -> (((@CFPrint.tag tag_let_trm (Label_create '_x4)
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (Logic.ex (fun Q1 : (((prod (list _A)) (list _B))
-> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag tag_apply
_ _ ((((@app_1 (list ((prod _A) _B))) ((prod (list
_A)) (list _B))) split) l)) H) Q1)) (forall _x4 : ((prod
(list _A)) (list _B)), (((@CFPrint.tag (tag_match 1%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
rx : (list _A), (forall ry : (list _B), (((Logic.eq
_x4) (rx,ry)) -> (((@CFPrint.tag tag_ret _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((pred_le H) (Q (((Coq.Lists.List.cons x) rx),((Coq.Lists.List.cons
y) ry)))))))) H) Q))))) ((forall rx : (list _A), (forall
ry : (list _B), (Logic.not ((Logic.eq _x4) (rx,ry)))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q))))))))
(Q1 _x4)) Q))))))))) H) Q)))))) ((forall x : _A, (forall
y : _B, (forall l : (list ((prod _A) _B)), (Logic.not
((Logic.eq _x0) ((Coq.Lists.List.cons (x,y)) l))))))
-> (((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q)))))))))) -> ((spec_1 K) split)))))))).

Hint
Extern 1 (RegisterCf split) => Provide split_cf.

Global
Instance combine_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter combine : CFSpec.func.

Parameter
combine_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _B : Type, (forall _A : Type,
(forall K : ((list _A) -> ((list _B) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop))), ((is_spec_2
K) -> ((forall l1 : (list _A), (forall l2 : (list _B),
(((K l1) l2) (@CFPrint.tag tag_let_val _ _ (local (fun
H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> (forall _x3 : ((prod (list _A)) (list _B)), (((Logic.eq
_x3) (l1,l2)) -> (((@CFPrint.tag (tag_match 3%nat)
_ _ (@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
_x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q Coq.Lists.List.nil))))))
H) Q))) ((Logic.not ((Logic.eq _x3) (Coq.Lists.List.nil,Coq.Lists.List.nil)))
-> (((@CFPrint.tag tag_case _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall
a1 : _A, (forall l1 : (list _A), (forall a2 : _B, (forall
l2 : (list _B), (((Logic.eq _x3) (((Coq.Lists.List.cons
a1) l1),((Coq.Lists.List.cons a2) l2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x8) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : ((list ((prod _A) _B)) -> CFHeaps.hprop) => ((Logic.and
(((@CFPrint.tag tag_apply _ _ ((((((@app_2 (list _A))
(list _B)) (list ((prod _A) _B))) combine) l1) l2))
H) Q1)) (forall _x8 : (list ((prod _A) _B)), (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q ((Coq.Lists.List.cons
(a1,a2)) _x8))))))) (Q1 _x8)) Q))))))))) H) Q)))))))
((forall a1 : _A, (forall l1 : (list _A), (forall a2
: _B, (forall l2 : (list _B), (Logic.not ((Logic.eq
_x3) (((Coq.Lists.List.cons a1) l1),((Coq.Lists.List.cons
a2) l2)))))))) -> (((@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (forall _p0 : (list _A), (forall _p1
: (list _B), (((Logic.eq _x3) (_p0,_p1)) -> (((@CFPrint.tag
tag_fail _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => False)))) H) Q))))) ((forall
_p0 : (list _A), (forall _p1 : (list _B), (Logic.not
((Logic.eq _x3) (_p0,_p1))))) -> (((@CFPrint.tag tag_done
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => True)))) H) Q))))))) H) Q)))))))
H) Q)))))))) H) Q)))))))))) -> ((spec_2 K) combine)))))))).

Hint
Extern 1 (RegisterCf combine) => Provide combine_cf.

Global
Instance merge_type_inhab : (Inhab CFSpec.func).

Proof.
inhab. Qed.



Parameter merge : CFSpec.func.

Parameter
merge_cf : (@CFPrint.tag tag_top_fun _ _ (@CFPrint.tag
tag_body _ _ (forall _A : Type, (forall K : (CFSpec.func
-> ((list _A) -> ((list _A) -> ((CFHeaps.hprop -> ((_
-> CFHeaps.hprop) -> Prop)) -> Prop)))), ((is_spec_3
K) -> ((forall cmp : CFSpec.func, (forall l1 : (list
_A), (forall l2 : (list _A), ((((K cmp) l1) l2) (@CFPrint.tag
tag_let_val _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => (forall _x3 : ((prod (list
_A)) (list _A)), (((Logic.eq _x3) (l1,l2)) -> (((@CFPrint.tag
(tag_match 3%nat) _ _ (@CFPrint.tag tag_case _ _ (local
(fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (forall l2 : (list _A), (((Logic.eq
_x3) (Coq.Lists.List.nil,l2)) -> (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q l2)))))) H) Q))))
((forall l2 : (list _A), (Logic.not ((Logic.eq _x3)
(Coq.Lists.List.nil,l2)))) -> (((@CFPrint.tag tag_case
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((Logic.and (forall l1 : (list _A),
(((Logic.eq _x3) (l1,Coq.Lists.List.nil)) -> (((@CFPrint.tag
tag_ret _ _ (local (fun H : CFHeaps.hprop => (fun Q
: (_ -> CFHeaps.hprop) => ((pred_le H) (Q l1))))))
H) Q)))) ((forall l1 : (list _A), (Logic.not ((Logic.eq
_x3) (l1,Coq.Lists.List.nil)))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall h1
: _A, (forall t1 : (list _A), (forall h2 : _A, (forall
t2 : (list _A), (((Logic.eq _x3) (((Coq.Lists.List.cons
h1) t1),((Coq.Lists.List.cons h2) t2))) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x6) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : (int -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 _A) _A) int) cmp) h1) h2))
H) Q1)) (forall _x6 : int, (((@CFPrint.tag tag_if _
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((Logic.and (((Logic.eq (((fun _y _z => istrue (_y
<= _z)) _x6) (0)%Z)) true) -> (((@CFPrint.tag tag_let_trm
(Label_create '_x20) _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex (fun
Q1 : ((list _A) -> CFHeaps.hprop) => ((Logic.and (((@CFPrint.tag
tag_apply _ _ ((((((((@app_3 CFSpec.func) (list _A))
(list _A)) (list _A)) merge) cmp) t1) l2)) H) Q1))
(forall _x20 : (list _A), (((@CFPrint.tag tag_ret _
_ (local (fun H : CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop)
=> ((pred_le H) (Q ((Coq.Lists.List.cons h1) _x20)))))))
(Q1 _x20)) Q))))))))) H) Q))) (((Logic.eq (((fun _y
_z => istrue (_y <= _z)) _x6) (0)%Z)) false) -> (((@CFPrint.tag
tag_let_trm (Label_create '_x13) _ (local (fun H :
CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) => (Logic.ex
(fun Q1 : ((list _A) -> CFHeaps.hprop) => ((Logic.and
(((@CFPrint.tag tag_apply _ _ ((((((((@app_3 CFSpec.func)
(list _A)) (list _A)) (list _A)) merge) cmp) l1) t2))
H) Q1)) (forall _x13 : (list _A), (((@CFPrint.tag tag_ret
_ _ (local (fun H : CFHeaps.hprop => (fun Q : (_ ->
CFHeaps.hprop) => ((pred_le H) (Q ((Coq.Lists.List.cons
h2) _x13))))))) (Q1 _x13)) Q))))))))) H) Q))))))) (Q1
_x6)) Q))))))))) H) Q))))))) ((forall h1 : _A, (forall
t1 : (list _A), (forall h2 : _A, (forall t2 : (list
_A), (Logic.not ((Logic.eq _x3) (((Coq.Lists.List.cons
h1) t1),((Coq.Lists.List.cons h2) t2)))))))) -> (((@CFPrint.tag
tag_done _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => True)))) H) Q))))))) H)
Q))))))) H) Q)))))))) H) Q))))))))))) -> ((spec_3 K)
merge))))))).

Hint Extern 1 (RegisterCf merge) =>
Provide merge_cf.

Global Instance chop_type_inhab
: (Inhab CFSpec.func).

Proof. inhab. Qed.



Parameter
chop : CFSpec.func.

Parameter chop_cf : (@CFPrint.tag
tag_top_fun _ _ (@CFPrint.tag tag_body _ _ (forall
_A : Type, (forall K : (int -> ((list _A) -> ((CFHeaps.hprop
-> ((_ -> CFHeaps.hprop) -> Prop)) -> Prop))), ((is_spec_2
K) -> ((forall k : int, (forall l : (list _A), (((K
k) l) (@CFPrint.tag tag_if _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((Logic.and (((Logic.eq
(((fun _y _z => istrue (_y = _z)) k) (0)%Z)) true)
-> (((@CFPrint.tag tag_ret _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => ((pred_le H) (Q
l)))))) H) Q))) (((Logic.eq (((fun _y _z => istrue
(_y = _z)) k) (0)%Z)) false) -> (((@CFPrint.tag (tag_match
2%nat) _ _ (@CFPrint.tag tag_case _ _ (local (fun H
: CFHeaps.hprop => (fun Q : (_ -> CFHeaps.hprop) =>
((Logic.and (forall x : _A, (forall t : (list _A),
(((Logic.eq l) ((Coq.Lists.List.cons x) t)) -> (((@CFPrint.tag
tag_apply _ _ ((((((@app_2 int) (list _A)) (list _A))
chop) ((Coq.ZArith.BinInt.Zminus k) (1)%Z)) t)) H)
Q))))) ((forall x : _A, (forall t : (list _A), (Logic.not
((Logic.eq l) ((Coq.Lists.List.cons x) t))))) -> (((@CFPrint.tag
tag_case _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => ((Logic.and (forall _p0
: (list _A), (((Logic.eq l) _p0) -> (((@CFPrint.tag
tag_fail _ _ (local (fun H : CFHeaps.hprop => (fun
Q : (_ -> CFHeaps.hprop) => False)))) H) Q)))) ((forall
_p0 : (list _A), (Logic.not ((Logic.eq l) _p0))) ->
(((@CFPrint.tag tag_done _ _ (local (fun H : CFHeaps.hprop
=> (fun Q : (_ -> CFHeaps.hprop) => True)))) H) Q)))))))
H) Q)))))))) H) Q)))))))))) -> ((spec_2 K) chop))))))).

Hint
Extern 1 (RegisterCf chop) => Provide chop_cf.
