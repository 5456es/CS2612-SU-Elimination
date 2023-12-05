Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Local Open Scope string.
Local Open Scope Z.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.SyntaxInCoq.
Require Import compcert.lib.Integers.
Require Import PL.PracticalDenotations.
Require Import PL.DenotationalSemantics.
Local Open Scope bool.
Local Open Scope string.
Local Open Scope Z.
Local Open Scope sets.

Require Import Coq.Lists.List.
Import ListNotations.


Definition struct_type_name := string.
Definition union_type_name := string.
Definition var_name := string.
Definition fieldname := string.
Definition union_case_name := string.
Definition SU_type_name := string.
Definition size := Z.
Module Type_defined.
Import Lang_WhileD.
Import Lang_While.

Inductive type : Type :=
  | TInt : type
  | TIntPtr : type->type
  | TBool : type
  | TStruct : struct_type_name->type
  | TUnion : union_type_name ->type
with  struct_field : Type :=
| StructField : fieldname -> type -> struct_field
with union_case : Type :=
| UnionCase : union_case_name -> type -> option expr -> union_case.
End Type_defined.


Module SU_Env.
Import Lang_WhileD.
Import Lang_While.
Import Type_defined.
Check (TStruct "a").
Inductive struct_info : Type :=
  | StructDef : struct_type_name->list struct_field -> struct_info.

Inductive union_info : Type :=
  | UnionDef : union_type_name->list union_case -> union_info.


  (* 定义变量名到类型的表格 *)
  Definition var_table : Type := list (var_name * type).

  (* 定义结构或联合类型和其内部结构的表格 *)
  Definition struct_union_table : Type := list (type * option struct_info * option union_info ).

  (* 将类型环境定义为这两个表格的二元组 *)
  Definition type_env : Type := (var_table * struct_union_table).

  (* 更新变量表格的示例 *)
  Definition update_var_table (env : type_env) (var : var_name) (ty : type) : type_env :=
    let (var_tbl, su_tbl) := env in
    ((var, ty) :: var_tbl, su_tbl).

  (* 更新结构或联合表格的示例 *)
  Definition update_struct_union_table (env : type_env) (ty : type) (sinfo : option struct_info) (uinfo : option union_info) : type_env :=
    let (var_tbl, su_tbl) := env in
    (var_tbl, (ty, sinfo, uinfo) :: su_tbl).

  
  (* 查询变量类型的函数 *)
  Fixpoint lookup_var_type (env : var_table) (var : var_name) : option type :=
    match env with
    | nil => None
    | (v, ty) :: rest => if string_dec v var then Some ty else lookup_var_type rest var
    end.
  
    (*---------------------------Example------Start-------------------*)
  (* 查询变量类型的示例 *)
  Definition example_lookup1 : option type :=
    let var_env : var_table := [("x", TInt); ("y", TBool)] in
    lookup_var_type var_env "x".

  (* 检查 (TStruct "a") 并更新表格的示例 *)
  Check (TStruct "a").

  (* 使用更新函数的示例 *)
  Definition example_env : type_env :=
    let initial_env : type_env := (nil, nil) in
    let env_after_var_update := update_var_table initial_env "x" TInt in
    let env_after_su_update := update_struct_union_table env_after_var_update (TStruct "a") (Some (StructDef "a" nil)) None in
    env_after_su_update.
      (*---------------------------Example------End-------------------*)


  (* 定义变量类型环境的初始状态 *)
  Definition initial_env : type_env := (nil, nil).


    (*---------------------------Example------Start-------------------*)

  (* 更新变量表格，添加变量 "x" 类型为 TInt *)
  Definition env_after_var_update : type_env := update_var_table initial_env "x" TInt.

  (* 查询变量 "x" 的类型 *)
  Definition example_lookup : option type :=
    let var_env : var_table := fst env_after_var_update in
    lookup_var_type var_env "x".

  (* 输出查询结果 *)
  Compute example_lookup. (* 应该输出 Some TInt *)
    (*---------------------------Example-------End------------------*)

  Require Import Coq.Strings.String.


  (* 定义提取结构体名的函数 *)
  Definition extract_struct_name (s : type) : struct_type_name :=
    match s with
    | TStruct sn => sn
    | _ => "notfind" (* 默认值，可能需要根据实际情况调整 *)
    end.



  (* 查询结构体内部结构的函数 *)
  Fixpoint lookup_struct_info (env : struct_union_table) (struct_name : struct_type_name) : option struct_info :=
    match env with
    | nil => None
    | (ty, sinfo, _) :: rest => if string_dec (extract_struct_name ty) struct_name then sinfo else lookup_struct_info rest struct_name
    end.

    Fixpoint check_sinfo (sinfo : option struct_info) : list struct_field :=
      match sinfo with
      | Some (StructDef _ fields) => fields
      | None => nil
      end.



      (*---------------------------Example------Start-------------------*)


      (* 查询结构体字段类型的函数 *)

      

     
      Definition lookup_field_type (sinfo : struct_info) (field_name : fieldname) : option type :=
        match sinfo with
        | StructDef _ fields =>
          match find (fun f => match f with StructField fname _ => if string_dec fname field_name then true else false end) fields with
          | Some (StructField _ field_type) => Some field_type
          | None => None
          end
        end.

    
    (*---------------------------Example------Start-------------------*)

  (* 定义结构体 A 的类型环境 *)
  Definition env_with_struct_A : type_env :=
    let initial_env : type_env := (nil, nil) in
    let env_after_struct_A :=
      update_struct_union_table initial_env (TStruct "AB") (Some (StructDef "AB" [StructField "x" TInt; StructField "y" TBool; StructField "s" (TStruct "CD")])) None
    in
    env_after_struct_A.

  (* 定义结构体 A z 的类型环境 *)
  Definition env_with_struct_A_and_z : type_env :=
    let struct_A_env : struct_union_table := snd (env_with_struct_A) in
    update_var_table env_with_struct_A "z" (TStruct "AB").

  (* 使用查询函数的例子，查询结构体 A 的内部结构 *)
  Definition example_query_struct_A : option struct_info :=
    let struct_A_env : struct_union_table := snd (env_with_struct_A) in
    lookup_struct_info struct_A_env "AB".
Compute example_query_struct_A.

  (* 使用查询函数的例子，查询变量 z 的类型 *)
  Definition example_query_z : option type :=
    let var_env : var_table := fst (env_with_struct_A_and_z) in
    lookup_var_type var_env "z".
    Definition example_query_z_x : option type :=
      match example_query_struct_A with
      | Some struct_A_info => lookup_field_type struct_A_info "s"
      | None => None
      end.
    Compute example_query_z.
    Compute example_query_z_x.
    (*---------------------------Example-------End------------------*)

Check type.
End SU_Env.









Module WhileDU.

Import Lang_WhileD.
Import Lang_While.
Import Type_defined.



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
nrm := arith_sem1_nrm Zfun D1.(nrm) D2.(nrm);
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

Definition or_sem (D1 D2: EDenote): EDenote :=
{|
nrm := or_sem_nrm D1.(nrm) D2.(nrm);
err := D1.(err) ∪ or_sem_err D1.(nrm) D2.(err);
|}.

Definition unop_sem (op: unop) (D: EDenote): EDenote :=
  match op with
  | ONeg => neg_sem D
  | ONot => not_sem D
  end.

Definition binop_sem (op: binop) (D1 D2: EDenote): EDenote :=
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


  Definition const_sem (n: Z): EDenote :=
    {|
      nrm := fun s i =>
               i = Int64.repr n /\
               Int64.min_signed <= n <= Int64.max_signed;
      err := fun s =>
               n < Int64.min_signed \/
               n > Int64.max_signed;
    |}.
  
(** 『解引用』表达式既可以用作右值也可以用作左值。其作为右值是的语义就是原先我们
    定义的『解引用』语义。*)

Definition deref_sem_nrm
(D1: state -> int64 -> Prop)
(s: state)
(i: int64): Prop :=
exists i1, D1 s i1 /\ s.(mem) i1 = Some (Vint i).

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

(** 基于此，可以又定义它作为右值时的值。*)

Definition var_sem_r (X: var_name): EDenote :=
deref_sem_r (var_sem_l X).




Inductive expr : Type :=
| EConst (n: Z) : expr
| EVar (x: var_name) : expr
| EBinop (op: binop) (e1 e2: expr) : expr
| EUnop (op: unop) (e: expr) : expr
| EDeref (e: expr) : expr
| EAddrOf (e: expr) : expr
(*| ECast (e: expr) (t: type) : expr   Type casting *)
| EStructMember (e: expr) (field: var_name) : expr  (* Access struct member *)
| EUnionMember (e: expr) (field: var_name) : expr.  (* Access union member *)


Fixpoint eval_r (e: expr): EDenote :=
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
with eval_l (e: expr): EDenote :=
  match e with
  | EVar X =>
      var_sem_l X
  | EDeref e1 =>
      eval_r e1
  | _ =>
      {| nrm := ∅; err := Sets.full; |}
  end.

Inductive com : Type :=
  | CSkip: com
  | CDecl (x: var_name) (t: type): com
  | CAsgn (x: var_name) (e: expr): com
  | CStructAsgn (x: var_name) (fields: list struct_field): com
  | CUnionAsgn (x: var_name) (cases: list union_case): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

 




