(* 大作业中带有类型定义和struct union 定义或声明, 变量定义的 Coq 语法文件 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope Z.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.SyntaxInCoq.
Require Import compcert.lib.Integers.
Require Import PL.PracticalDenotations.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Require Import Coq.Lists.List.
Import ListNotations.

Import Lang_WhileD.
Import Lang_While.


Inductive expr_malloc : Type :=
| EConst (n: Z)  : expr_malloc
| EVar (x: var_name) : expr_malloc
| EBinop (op: binop) (e1 e2: expr_malloc) : expr_malloc
| EUnop (op: unop) (e: expr_malloc) : expr_malloc
| EDeref (e: expr_malloc) : expr_malloc
| EAddrOf (e: expr_malloc) : expr_malloc.

Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

Module EDenote.

Record EDenote: Type := {
  nrm: state -> int64 -> Prop;
  err: state -> Prop;
}.

End EDenote.

Import EDenote.

Notation "x '.(nrm)'" := (EDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (EDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote.nrm x).

Ltac any_err x := exact (EDenote.err x).

Notation "x '.(nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(err)'" := (ltac:(any_err x))
  (at level 1, only parsing).

  Definition arith_sem1_nrm
  (Zfun: Z -> Z -> Z)
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1 i2,
D1 s i1 /\ D2 s i2 /\
arith_compute1_nrm Zfun i1 i2 i.

Definition arith_sem1_err
  (Zfun: Z -> Z -> Z)
  (D1 D2: state -> int64 -> Prop)
  (s: state): Prop :=
exists i1 i2,
D1 s i1 /\ D2 s i2 /\
arith_compute1_err Zfun i1 i2.

Definition arith_sem1 Zfun (D1 D2: EDenote): EDenote :=
{|
nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm)    ;
err := D1.(err) ∪ D2.(err) ∪
arith_sem1_err Zfun D1.(nrm) D2.(nrm);
|}.



Definition arith_sem2_nrm
             (int64fun: int64 -> int64 -> int64)
             (D1 D2: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_nrm int64fun i1 i2 i.

Definition arith_sem2_err
             (D1 D2: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1 i2,
    D1 s i1 /\ D2 s i2 /\
    arith_compute2_err i1 i2.

Definition arith_sem2 int64fun (D1 D2: EDenote): EDenote :=
  {|
    nrm := arith_sem2_nrm int64fun D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ D2.(err) ∪
           arith_sem2_err D1.(nrm) D2.(nrm);
  |}.

  Definition cmp_sem_nrm
  (c: comparison)
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1 i2,
D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote): EDenote :=
{|
nrm := cmp_sem_nrm c D1.(nrm) D2.(nrm);
err := D1.(err) ∪ D2.(err);
|}.

Definition neg_sem_nrm
  (D1: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1, D1 s i1 /\ neg_compute_nrm i1 i.



Definition neg_sem_err
             (D1: state -> int64 -> Prop)
             (s: state): Prop :=
  exists i1, D1 s i1 /\ neg_compute_err i1.

Definition neg_sem (D1: EDenote): EDenote :=
  {|
    nrm := neg_sem_nrm D1.(nrm);
    err := D1.(err) ∪ neg_sem_err D1.(nrm);
  |}.

Definition not_sem_nrm
             (D1: state -> int64 -> Prop)
             (s: state)
             (i: int64): Prop :=
  exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote): EDenote :=
  {|
    nrm := not_sem_nrm D1.(nrm);
    err := D1.(err);
  |}.

  Definition and_sem_nrm
  (D1 D2: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1,
D1 s i1 /\
(SC_and_compute_nrm i1 i \/
NonSC_and i1 /\
exists i2,
D2 s i2 /\ NonSC_compute_nrm i2 i).
Definition and_sem_err
             (D1: state -> int64 -> Prop)
             (D2: state -> Prop)
             (s: state): Prop :=
  exists i1,
    D1 s i1 /\ NonSC_and i1 /\ D2 s.

Definition and_sem (D1 D2: EDenote): EDenote :=
  {|
    nrm := and_sem_nrm D1.(nrm) D2.(nrm);
    err := D1.(err) ∪ and_sem_err D1.(nrm) D2.(err);
  |}.

  
Definition or_sem_nrm
(D1 D2: state -> int64 -> Prop)
(s: state)
(i: int64): Prop :=
exists i1,
D1 s i1 /\
(SC_or_compute_nrm i1 i \/
NonSC_or i1 /\
exists i2,
D2 s i2 /\ NonSC_compute_nrm i2 i).

Definition or_sem_err
(D1: state -> int64 -> Prop)
(D2: state -> Prop)
(s: state): Prop :=
exists i1,
D1 s i1 /\ NonSC_or i1 /\ D2 s.

Definition or_sem (D1 D2: EDenote) : EDenote :=
{|
nrm := or_sem_nrm D1.(nrm) D2.(nrm) ;
err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
|}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg =>  D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote) : EDenote :=
  match op with
  | OOr => or_sem D1 D2
  | OAnd => and_sem D1 D2
  | OLt => cmp_sem Clt D1 D2
  | OLe => cmp_sem Cle D1 D2
  | OGt => cmp_sem Cgt D1 D2
  | OGe => cmp_sem Cge D1 D2
  | OEq => cmp_sem Ceq D1 D2
  | ONe => cmp_sem Cne D1 D2
  | OPlus => arith_sem1 Z.add D1 D2 
  | OMinus => arith_sem1 Z.sub D1 D2 
  | OMul => arith_sem1 Z.mul D1 D2 
  | ODiv => arith_sem2 Int64.divs D1 D2
  | OMod => arith_sem2 Int64.mods D1 D2
  end.

(*这里认为常数指针和值在处理上是一样的，在使用时会因为type不同产生区别*)
  Definition const_sem (n: Z) : EDenote :=
    {|
      nrm := fun s i =>
               i = Int64.repr n /\
               Int64.min_signed <= n <= Int64.max_signed ;
      err := fun s =>
               n < Int64.min_signed \/
               n > Int64.max_signed ;
    |}.
  
(** 『解引用』表达式既可以用作右值也可以用作左值。其作为右值是的语义就是原先我们
    定义的『解引用』语义。*)

Definition deref_sem_nrm
(D1: state -> int64 -> Prop)
(s: state)
(i: int64): Prop :=
exists i1, D1 s i1 /\ s.(mem)  i1 = Some (Vint i).

(*这里的i1是地址*)

Definition deref_sem_err
(D1: state -> int64 -> Prop)
(s: state): Prop :=
exists i1,
D1 s i1 /\
(s.(mem) i1 = None \/ s.(mem) i1 = Some Vuninit).

Definition deref_sem_r (D1: EDenote): EDenote :=
{|
nrm := deref_sem_nrm D1.(nrm);
err := D1.(err) ∪ deref_sem_err D1.(nrm);
|}.



(** 当程序表达式为单个变量时，它也可以同时用作左值或右值。下面先定义其作为左值时
的存储地址。*)

Definition var_sem_l (X: var_name): EDenote :=
{|
nrm := fun s i => s.(env) X = i;
err := ∅;
|}.

(*
Definition noSU_var_sem_l (X: var_name): EDenote :=
{|
nrm := fun s i => s.(env) X = i /\ (s.(type_env) X) <> TStruct X /\ (s.(type_env) X) <> TUnion X;
err := ∅;
|}.*)

(** 基于此，可以又定义它作为右值时的值。*)
(** 基于此，可以又定义它作为右值时的值。*)



Definition var_sem_r (X: var_name): EDenote :=
  deref_sem_r (var_sem_l X).


  (**此处，定义一个False的语句**)

  Definition False_sem: EDenote :=
    {|
    nrm := ∅;
    err := Sets.full;
    |}.
    
    





  Fixpoint eval_r (e: expr_malloc): EDenote :=
    match e with
    | EConst n =>
        const_sem n
    | EVar X =>
        var_sem_r X
    | EBinop op e1 e2 =>
        binop_sem op (eval_r e1) (eval_r e2)
    | EUnop op e1 =>
        unop_sem op (eval_r e1)
    | EDeref e1 =>
        deref_sem_r (eval_r e1)
    | EAddrOf e1 =>
        eval_l e1
    end
  with eval_l (e: expr_malloc): EDenote :=
    match e with
    | EVar X =>
        var_sem_l X
    | EDeref e1 =>
        eval_r e1
    | _ =>
        {| nrm := ∅; err := Sets.full; |}
    end.


  Definition test_true (D: EDenote):
  state -> state -> Prop :=
  Rels.test
    (fun s =>
       exists i, D.(nrm) s i /\ Int64.signed i <> 0).

Definition test_false (D: EDenote):
  state -> state -> Prop :=
  Rels.test (fun s => D.(nrm) s (Int64.repr 0)).

Module CDenote.


Record CDenote: Type := {
  nrm: state -> state -> Prop;
  err: state -> Prop;
  inf: state -> Prop
}.

End CDenote.
Import CDenote.
(*
Definition SU_state_staysame (s1 s2: state): Prop :=

  s1.(struct_info) = s2.(struct_info) /\
  s1.(union_info) = s2.(union_info) /\
  s1.(type_size) = s2.(type_size).
*)




Notation "x '.(nrm)'" := (CDenote.nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote.err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote => exact (EDenote.nrm x)
  | CDenote => exact (CDenote.nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote => exact (EDenote.err x)
  | CDenote => exact (CDenote.err x)
  end.

Definition skip_sem: CDenote :=
  {|
    nrm := Rels.id;
    err := ∅;
    inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote): CDenote :=
  {|
    nrm := D1.(nrm) ∘ D2.(nrm);
    err := D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
    inf := D1.(inf) ∪ (D1.(nrm) ∘ D2.(inf));
  |}.

Definition if_sem
             (D0: EDenote)
             (D1 D2: CDenote): CDenote :=
  {|
    nrm := (test_true D0 ∘ D1.(nrm)) ∪
           (test_false D0 ∘ D2.(nrm));
    err := D0.(err) ∪
           (test_true D0 ∘ D1.(err)) ∪
           (test_false D0 ∘ D2.(err));
    inf := (test_true D0 ∘ D1.(inf)) ∪
           (test_false D0 ∘ D2.(inf))
  |}.

Fixpoint boundedLB_nrm
           (D0: EDenote)
           (D1: CDenote)
           (n: nat):
  state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      (test_true D0 ∘ D1.(nrm) ∘ boundedLB_nrm D0 D1 n0) ∪
      (test_false D0)
  end.

Fixpoint boundedLB_err
           (D0: EDenote)
           (D1: CDenote)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 ∘
        ((D1.(nrm) ∘ boundedLB_err D0 D1 n0) ∪
         D1.(err))) ∪
      D0.(err)
  end.

Definition is_inf
             (D0: EDenote)
             (D1: CDenote)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 ∘ ((D1.(nrm) ∘ X) ∪ D1.(inf)).

Definition while_sem
             (D0: EDenote)
             (D1: CDenote): CDenote :=
  {|
    nrm := ⋃ (boundedLB_nrm D0 D1);
    err := ⋃ (boundedLB_err D0 D1);
    inf := Sets.general_union (is_inf D0 D1);
  |}.

(** 向地址赋值的语义与原先定义基本相同，只是现在需要规定所有变量的地址不被改变，
    而非所有变量的值不被改变。*)

Definition asgn_deref_sem_nrm
             (D1 D2: state -> int64 -> Prop)
             (s1 s2: state): Prop :=
  exists i1 i2,
    D1 s1 i1 /\
    D2 s1 i2 /\
    s1.(mem) i1 <> None /\
    s2.(mem) i1 = Some (Vint i2) /\
    (forall X, s1.(env) X = s2.(env) X) /\
    (forall p, i1 <> p -> s1.(mem) p = s2.(mem) p).

Definition asgn_deref_sem_err
             (D1: state -> int64 -> Prop)
             (s1: state): Prop :=
  exists i1,
    D1 s1 i1 /\
    s1.(mem) i1 = None.

Definition asgn_deref_sem
             (D1 D2: EDenote): CDenote :=
  {|
    nrm := (asgn_deref_sem_nrm D1.(nrm) D2.(nrm));
    err := D1.(err) ∪ D2.(err) ∪
           asgn_deref_sem_err D2.(nrm);
    inf := ∅;
  |}.

(** 变量赋值的行为可以基于此定义。*)




Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote): CDenote :=
  asgn_deref_sem (var_sem_l X) D1.

Check 12.
(* 定义 int64 序列生成函数 *)
(*经过语法变换，在whileD+malloc中的declare语句应该传递两个参数，变量名和需要的地址数*)
Definition declare_sem_malloc (X: var_name) (sz: Z): CDenote :=
{|
    nrm:= fun s1 s2 =>
            forall i, s1.(env) X <> i /\
            exists i': int64, (s2.(env) X = i' /\
            ((s1.(mem) i') <> None)) /\
            forall k: Z, 0 <= k < sz -> ((s1.(mem) (Int64.add i' (Int64.repr k)) = Some Vuninit) /\
            (s2.(mem) (Int64.add i' (Int64.repr k)) = Some (Vint (Int64.repr 0))) /\
            (forall k': Z, k' < (Int64.unsigned i') \/ k' >= (Int64.unsigned i')+sz -> s1.(mem) (Int64.repr k') = s2.(mem) (Int64.repr k')) /\
            (forall X', X' <> X -> s1.(env) X' = s2.(env) X')
            );(**)
    err:= fun s =>exists i, s.(env) X = i;
    inf := ∅;
|}.

Definition Zseq (start len : Z) : list Z :=
  List.map Z.of_nat (List.seq (Z.to_nat start) (Z.to_nat len)).
