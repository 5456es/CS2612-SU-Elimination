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

Module Lang_WhileDU3.
Import Lang_WhileD.
Import Lang_While.





Inductive type : Type :=
| TInt : type
| TPointer (t: type) : type
| TStruct (x: string) : type
| TUnion (x: string) : type
with men_var : Type :=
| MVar  (men_type : type) (var_name:  string) :  men_var.


Inductive expr : Type :=
| EConst (n: Z) (ty : type) : expr
| EVar (x: var_name) (ty:type): expr
| EBinop (op: binop) (e1 e2: expr)(ty:type) : expr
| EUnop (op: unop) (e: expr)(ty:type) : expr
| EDeref (e: expr)(ty:type) : expr
| EAddrOf (e: expr) (ty:type): expr
(*| ECast (e: expr) (t: type) : expr   Type casting *)
| EStructMember (x:expr) (field: var_name) (ty:type): expr  (* Access struct member *)
| EUnionMember (x:expr) (field: var_name)(ty:type) : expr  (* Access union member *)
| EPoniter_Struct_Member (x:expr) (field: var_name)(ty:type) : expr  (* Access poniter member *)
| EPoniter_Union_Member (x:expr) (field: var_name)(ty:type) : expr  (* Access poniter member *).



Record state : Type := {
  type_env : var_name -> type;
  env : var_name -> int64;
  mem : int64 -> option val;
  struct_info : string -> list men_var;
  union_info :  string->list men_var;
  type_size : type -> Z;

  type_size_properties :
    type_size TInt = 1 ->
    (forall t : type, type_size (TPointer t) = 1) ->
    (forall x : string, type_size (TStruct x) = 
        fold_left (fun acc field =>
        match field with
        | MVar ty name => acc + type_size ty
      end) (struct_info x) 0) ->
    (forall x : string, type_size (TUnion x) =
        fold_left (fun acc field =>
            match field with
            | MVar ty name => Z.max acc (type_size ty)
        end) (union_info x) 0) ->True
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


Definition NotStructOrUnion (ty1 ty2:type)(s: state)
(i: int64): Prop := 
            forall su , ty1 <> TStruct su /\  
                        ty1 <> TUnion su /\ 
                        ty2 <> TStruct su /\ 
                        ty2 <> TUnion su.





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


  Definition const_sem (n: Z): EDenote :=
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

Definition False_sem: EDenote :=
{|
nrm := ∅;
err := Sets.full;
|}.



Definition var_sem_r (X: var_name) : EDenote :=
  {|
    nrm := (fun s i => forall su , s.(type_env) X <> TStruct su /\ s.(type_env) X <> TUnion su) ∩ (deref_sem_r (var_sem_l X)).(nrm);
    err := (fun s  => forall su ,s.(type_env) X = TStruct su \/ s.(type_env) X = TUnion su) ∪ (deref_sem_r (var_sem_l X)).(err);
  |}.






(* 辅助函数：计算结构体中字段的偏移量 *)
Fixpoint calculate_offset (s:state) (field: string) (fields: list men_var) (offset: Z) : option Z :=
  match fields with
  | [] => None (* 未找到字段，返回 None *)
  | MVar ty f :: rest =>
    if string_dec f field
    then Some offset (* 找到字段，返回当前偏移量 *)
    else calculate_offset s field rest (offset + s.(type_size) ty ) (* 继续查找下一个字段 *)
  end.


(* 辅助函数：查找结构体中字段的偏移量 *)
Definition find_field_offset (s : state) (field: string) (struct_fields: list men_var) : option Z :=
  calculate_offset s field struct_fields (0).

(* 主要函数：结构体成员的正常状态 *)
Definition struct_member_sem_nrm (x: string) (field: string) (s: state) (i: int64): Prop :=
  match s.(type_env) x with
  | TStruct x' =>
    match find_field_offset s field (s.(struct_info) x') with
    | Some offset =>
      exists i', s.(env) x = i' /\ s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vint i)
    | None => False
    end
  | _ => False
  end.

  (*struct A x
  A{b C d}

  x ->??????
  x.C.d*)



  Definition struct_member_sem_err (x: string) (field: string) (s: state): Prop :=
    match s.(type_env) x with
    | TStruct x' =>
      match find_field_offset s field (s.(struct_info) x') with
      | Some offset =>
        exists i', s.(env) x = i' /\
                   (s.(mem) (Int64.add i' (Int64.repr offset)) = None \/(
                     s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vuninit)) )
      | None => True
      end
    | _ => True
    end.

Definition struct_menber_sem (x: string) (field: string): EDenote :=
{|
  nrm := struct_member_sem_nrm x field;
  err := struct_member_sem_err x field;
|}.

Definition union_member_sem_nrm (x: string) (case: string) (s: state) (i: int64): Prop :=
  match s.(type_env) x with
  | TUnion x' =>
    match find_field_offset s case (s.(union_info) x') with
    | Some offset =>
      exists i', s.(env) x = i' /\ s.(mem) i' = Some (Vint i)
    | None => False
    end
  | _ => False
    end.
  
Definition union_member_sem_err (x: string) (case: string) (s: state): Prop :=
  match s.(type_env) x with
  | TUnion x' =>
    match find_field_offset s case (s.(union_info) x') with
    | Some offset =>
      exists i', s.(env) x = i' /\
                 (s.(mem) i' = None \/(
                   s.(mem) i' = Some (Vuninit)) )
    | None => True
    end
  | _ => True
  end.

  Definition union_menber_sem (x: string) (case: string): EDenote :=
{|
  nrm := union_member_sem_nrm x case;
  err := union_member_sem_err x case;
|}.
  

Definition EPoniterMember_sem_nrm (x:var_name) (field: var_name) (s:state) (i :int64): Prop:=  (* Access poniter member *)
    match s.(type_env) x with
    | TPointer pointed_type =>
      match pointed_type with

        | TStruct x' =>
          match find_field_offset s field (s.(struct_info) x') with
          | Some offset =>
            exists i', s.(mem) (s.(env) x) = Some (Vint i') /\ s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vint i)
          | None => False
          end  

        | TUnion x' =>
          match find_field_offset s field (s.(union_info) x') with
          | Some offset =>
            exists i', s.(mem) (s.(env) x) = Some (Vint i') /\ s.(mem) i' = Some (Vint i)
          | None => False
          end
        | _ => False
        end
      | _ => False
    end.

Definition EPoniterMember_sem_err (x:var_name) (field: var_name) (s:state): Prop:=  (* Access poniter member *)
    match s.(type_env) x with
    | TPointer pointed_type =>
      match pointed_type with

        | TStruct x' =>
          match find_field_offset s field (s.(struct_info) x') with
          | Some offset =>
             s.(mem) (s.(env) x) = Some (Vuninit ) \/ ( exists i',s.(mem) (s.(env) x) = Some (Vint i') /\ (s.(mem) (Int64.add i' (Int64.repr offset)) = None \/ s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vuninit)))
          | None => True
          end  

        | TUnion x' =>
          match find_field_offset s field (s.(union_info) x') with
          | Some offset =>
          s.(mem) (s.(env) x) = Some (Vuninit ) \/ ( exists i', s.(mem) (s.(env) x)= Some (Vint i') /\ (s.(mem) i' = None \/ s.(mem) i' = Some (Vuninit)))
          | None => True
          end
        | _ => True
        end
      | _ => True
    end.

Definition EPoniterMember_sem (x:var_name) (field: var_name): EDenote :=
{|
  nrm := EPoniterMember_sem_nrm x field;
  err := EPoniterMember_sem_err x field;
|}.





(*
Inductive expr : Type :=
| EConst (n: Z) (ty : type) : expr
| EVar (x: var_name) (ty:type): expr
| EBinop (op: binop) (e1 e2: expr)(ty :type) : expr
| EUnop (op: unop) (e: expr)(ty:type) : expr
| EDeref (e: expr) (ty:type) : expr
| EAddrOf (e: expr) (ty:type): expr
(*| ECast (e: expr) (t: type) : expr   Type casting *)
| EStructMember (x:expr) (field: var_name) (ty:type): expr  (* Access struct member *)
| EUnionMember (x:expr) (field: var_name)(ty:type) : expr  (* Access union member *)
| EPoniter_Struct_Member (x:expr) (field: var_name) (ty:type) : expr  (* Access poniter member *)
| EPoniter_Union_Member (x:expr) (field: var_name) (ty:type) : expr  (* Access poniter member *).
*)










Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n ty =>
      match ty with
      | TInt => const_sem n
      | _ => False_sem
      end
  | EVar X ty =>
      match ty with
      | TInt => var_sem_r X
      | TPointer _ => var_sem_r X
      | _ => False_sem
      end
  | EBinop op e1 e2  ty=>
      match ty with
      | TStruct _ => False_sem
      | TUnion _ => False_sem
      | _ => binop_sem op (eval_r e1) (eval_r e2) 
      end
  | EUnop op e1  ty=>
      match ty with
      | TInt => unop_sem op (eval_r e1)
      | TPointer _ => unop_sem op (eval_r e1)
      | _ => False_sem
        end
  | EDeref e1 ty=>
      deref_sem_r (eval_r e1)
  | EAddrOf e1 ty=>
      eval_l e1
  | EStructMember x field ty => (*x.y*)
      struct_menber_sem x field
  | EUnionMember x field ty=>
      union_menber_sem x field
  |EPoniter_Struct_Member   x field ty=>
      union_menber_sem x field
  | EPoniter_Union_Member x field ty=>
      union_menber_sem x field
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





  
1.union?怎么看
2. mem 取值的时候考不考虑类型
3.允不允许x.y.z 。。。。





