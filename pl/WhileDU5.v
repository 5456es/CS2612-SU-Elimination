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

Definition type_equal (ty1 ty2: type): Prop := 
  ty1 = ty2.



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


Definition noSU_var_sem_l (X: var_name): EDenote :=
{|
nrm := fun s i => s.(env) X = i /\ (s.(type_env) X) <> TStruct X /\ (s.(type_env) X) <> TUnion X;
err := ∅;
|}.

(** 基于此，可以又定义它作为右值时的值。*)
(** 基于此，可以又定义它作为右值时的值。*)



Definition var_sem_r (X: var_name) (ty : type) : EDenote :=
  {|
    nrm := (fun s i => s.(type_env) X = ty) ∩ (deref_sem_r (var_sem_l X)).(nrm);
    err := (fun s  => s.(type_env) X <> ty) ∪ (deref_sem_r (var_sem_l X)).(err);
  |}.


  (**此处，定义一个False的语句**)

  Definition False_sem: EDenote :=
    {|
    nrm := ∅;
    err := Sets.full;
    |}.
    
    




(*
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
Definition struct_menber_sem (x: string) (field: string) (ty:type): EDenote :=
{|
  nrm := struct_member_sem_nrm x field;
  err := struct_member_sem_err x field;
|}.

(*
Definition struct_menber_sem (x: expr) (field: string): EDenote :=
{|
  nrm := match x with
          | EStructMember x' field' ty=> struct_menber_sem x' field'
          | EUnionMember x' field' => union_menber_sem x' field'
          | EVar 
4477  err := struct_member_sem_err x field;
|}.
*)

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
*)

(*辅助函数：查找结构体中某个字段的类型*)
Fixpoint calculate_type (s:state) (field:string)(fields:list men_var) : option type := 
  match fields with
  | [] => None
  | MVar ty f :: rest =>
    if string_dec f field
    then Some ty
    else calculate_type s field rest
  end.

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

  (* x.y的处理：
      这个函数接受x的左值 对应struct_type 内部字段 
      返回这个字段的左值，也就是对应地址
      *)
Definition EStructMember_sem_l (D1: EDenote) (struct_type: string) (field: string) (ty:type) : EDenote :=
  {|
    nrm := (fun s i => exists i' , (D1.(nrm) s i' )/\ (
                                  match find_field_offset s field (s.(struct_info) struct_type) with
                                  (*查一下这个字段field在D1对应的struct Type里的偏移量*)
                                  | Some offset => i = Int64.add i' (Int64.repr offset)
                                  | None => False
                                  end) /\ calculate_type s field (s.(struct_info) struct_type) = Some ty
                                   );
    err := D1.(err) ∪ (fun s => exists i', (D1.(nrm) s i') /\ 
                                  (
                                  match find_field_offset s field (s.(struct_info) struct_type) with
                                  | Some offset => False
                                  | None => True
                                    end 
                                 
                                  )
                      );
  |}. 

  Definition EUnionMember_sem_l (D1: EDenote) (union_type: string) (field: string) (ty:type): EDenote :=
    {|
      nrm := (fun s i => exists i' , (D1.(nrm) s i' )/\ (
                                    match find_field_offset s field (s.(union_info) union_type) with
                                    (*查一下这个字段field在D1对应的union Type里的"偏移"量*)
                                    | Some offset => i =  i' 
                                    | None => False
                                    end) /\ calculate_type s field (s.(union_info) union_type) = Some ty
                                    );
      err := D1.(err) ∪ (fun s => exists i', (D1.(nrm) s i') /\ (
                                    match find_field_offset s field ( (s.(union_info) union_type)) with
                                    | Some offset => False
                                    | None => True
                                    end ));
    |}. 
  


(*StructMember_sem_r*)

Definition struct_member_sem_r (x:EDenote) (struct_type: string)(field:string)(ty:type): EDenote :=
{|
  nrm :=  fun s i => exists i', (x.(nrm) s i') /\ (
                                                match find_field_offset s field (s.(struct_info) struct_type) with
                                                (*查一下这个字段field在x对应的struct Type里的偏移量*)
                                                None => False
                                                | Some offset => s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vint i)
                                                end  /\ calculate_type s field (s.(struct_info) struct_type) = Some ty);
  err := x.(err) ∪ (fun s => exists i', (x.(nrm) s i') /\ (
                                                match find_field_offset s field (s.(struct_info) struct_type) with
                                                | None => True
                                                | Some offset => s.(mem) (Int64.add i' (Int64.repr offset)) = None \/ s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vuninit)
                                                end ));
|}.

Definition union_member_sem_r (x:EDenote) (union_type: string)(field:string)(ty:type): EDenote :=
{|
  nrm :=  fun s i => exists i', (x.(nrm) s i') /\ (
                                                match find_field_offset s field (s.(union_info) union_type) with
                                                (*查一下这个字段field在x对应的union Type里的"偏移"量*)
                                                None => False
                                                | Some offset => s.(mem) i' = Some (Vint i)
                                                end  /\ calculate_type s field (s.(union_info) union_type) = Some ty);
  err := x.(err) ∪ (fun s => exists i', (x.(nrm) s i') /\ (
                                                match find_field_offset s field (s.(union_info) union_type) with
                                                | None => True
                                                | Some offset => s.(mem) i' = None \/ s.(mem) i' = Some (Vuninit)
                                                end ));


|}.



(*感觉表达式加入类型作为参数在语法上显得有些奇怪，但是暂时没有什么更好的思路
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
*)

Definition expr_type_extract (e:expr): type :=
  match e with
  | EConst n ty => ty
  | EVar x ty => ty
  | EBinop op e1 e2 ty => ty
  | EUnop op e ty => ty
  | EDeref e ty => ty
  | EAddrOf e ty => ty
  | EStructMember x field ty => ty
  | EUnionMember x field ty => ty
  | EPoniter_Struct_Member x field ty => ty
  | EPoniter_Union_Member x field ty => ty
  end.



Fixpoint eval_r (e: expr): EDenote :=
  match e with
  | EConst n ty =>
      match ty with
      | TInt => const_sem n
      | _ => False_sem
      end
    
  | EVar X ty =>
      match ty with
      | TInt => var_sem_r X ty
      | TPointer _ => var_sem_r X ty
      | _ => False_sem
      end
      (*基于区分左右值的思路，右值只能是TInt 或者 TPointer*)

  | EBinop op e1 e2 ty=>
    (*此处我们认为只有TInt 和 TPointer 可以进行二元运算*)
      match expr_type_extract e1 as t1 with
        | TStruct _ => False_sem
        | TUnion _ => False_sem
        | TInt => 
          match expr_type_extract e2 with
          | TStruct _ => False_sem
          | TUnion _ => False_sem
          | TInt =>
            match ty with
            | TInt => binop_sem op (eval_r e1) (eval_r e2)
            | _ => False_sem
            end
          | TPointer _ =>
            match ty with
            | TInt => binop_sem op (eval_r e1) (eval_r e2)
            | _ => False_sem
            end
          end
        | TPointer pointer_type => 
          match expr_type_extract e2 with
          | TStruct _ => False_sem
          | TUnion _ => False_sem
          | TInt =>
            match ty with
            | TInt => binop_sem op (eval_r e1) (eval_r e2)
            | _ => False_sem
            end
          | TPointer pointer_type =>
            match ty with
            | TPointer pointer_type => binop_sem op (eval_r e1) (eval_r e2)
              (*这里值得注意的是，遇到了俩pointer，那么必须一致指向类型*)
            | _ => False_sem
          end
        end
      end 
  | EUnop op e1 ty=>
      match expr_type_extract e1 as t1 with
      | TStruct _ => False_sem
      | TUnion _ => False_sem
      (*老样子，右值不允许SU*)
      | TInt => unop_sem op (eval_r e1)
      | TPointer _ => unop_sem op (eval_r e1)
      end

  | EDeref e1 ty=>
      match expr_type_extract e1  with
      | TPointer pointer_type => 
            match pointer_type with
            | ty => deref_sem_r  (eval_r e1)
            end
      | _ => False_sem
      end
    
      (*eval_r e1 返回了什么？返回了的是一个Edenote ， 是 state->int64， 是返回了int64，那么你随便解析吧*)

  | EAddrOf e1 ty=>
    match ty with
    | TPointer pointed_type =>
      match expr_type_extract e1 with
      | pointed_type => eval_l e1

      end
    | _ => False_sem
      end


      (*这里的e1必须是个左值，那么我们就需要一个eval_l*)
      
      
      (*这里后面会判断，是个Var，那没关系，我们总是能通过state.env 找到这个变量的位置
        是个Dref？也没关系，反向回去好了。
      *)



  | EStructMember x field ty => 
    match ty with
    | TStruct _ => False_sem
    | TUnion _ => False_sem 
    | _ => 
      match expr_type_extract x with
      | TStruct struct_type =>   struct_member_sem_r (eval_l x) struct_type field ty
      | _ => False_sem
      end
    end
      (*如果出现嵌套，那么这个表达式应该需要一个地址*)


  (* ---弃案---
    让我们思考一下
      x.y
        x是个什么？是个expr!
        这个expression的类型是什么？是个struct！
        我们想想，什么东西能确认是这玩意儿？
        看看所有的expr，有哪些能够确认是struct的？
          1. EStructMember x field ty
          2. EUnionMember x field ty
          3. EPoniter_Struct_Member x field ty
          4. EPoniter_Union_Member x field ty
          5. EVar x ty
          6. EDeref x ty ？？？？？？？ 这玩意儿可以吗？？？？？？？？
            我觉得不行，因为这个东西的检验：【是个int64】所以不行


      类型确认后，我们怎么计算x.y呢？
      我们是按照偏移量来看的，所以我们需要知道x的地址，然后加上偏移量，就是y的地址了
  *)

  (*最新思路：
          x.y.z
          这里的x不管是什么，当作左值计算！！！！！
            所以下面的左值计算需要处理
          然后，然后根据类型，计算偏移量，然后加上x的地址，就是y的地址了

  *)
  | EUnionMember x field ty=>
      match ty with
      | TStruct _ => False_sem
      | TUnion _ => False_sem
      | _ => 
        match expr_type_extract x with
        | TUnion union_type => union_member_sem_r (eval_l x) union_type field ty
        | _ => False_sem
        end
      end  

  |EPoniter_Struct_Member x field ty=>
    match ty with
    | TStruct _ => False_sem
    | TUnion _ => False_sem
    | _ => 
      match expr_type_extract x with
      | TPointer pointed_type =>
        match pointed_type with
        | TStruct struct_type => struct_member_sem_r (eval_r x) struct_type field ty
        | _ => False_sem
        end
      | _ => False_sem
      end
    end
  
  | EPoniter_Union_Member x field ty=>
    match ty with
    | TStruct _ => False_sem
    | TUnion _ => False_sem
    | _ => 
      match expr_type_extract x with
      | TPointer pointed_type =>
        match pointed_type with
        | TUnion union_type => union_member_sem_r (eval_r x) union_type field ty
        | _ => False_sem
        end
      | _ => False_sem
      end
    end
   
  end
  with eval_l (e: expr): EDenote :=
  (*好，让我们想想能对什么东西计算左值
    1. EVar x ty （无条件）
    2. EDeref x ty （无条件）
    3. EStructMember x field ty
        这个玩意儿。。。。。的话，需要x的左值+ field在x这个struct中的偏移量
    4. EUnionMember x field ty
    5. EPoniter_Struct_Member x field ty
    6. EPoniter_Union_Member x field ty
  
  *)
  match e with
  | EVar X ty=>
      var_sem_l X
  | EDeref e1 ty =>
      eval_r e1
  | EStructMember x field ty =>
      match expr_type_extract x with 
      | TStruct struct_type => EStructMember_sem_l (eval_l x) struct_type field ty
      | _ => False_sem
      end
  | EUnionMember x field ty=>
      match expr_type_extract x with
      | TUnion union_type => EUnionMember_sem_l (eval_l x) union_type field ty
      | _ => False_sem
      end
      
  | EPoniter_Struct_Member x field ty=>
    (*对于 x->y 来说，这玩意儿的左值
      就是说x是个指针，指向的是个struct
      那么对应的地址应该是 x的右值 + field在x这个struct中的偏移量
    *)
      match expr_type_extract x with
      | TPointer pointed_type =>
        match pointed_type with
        | TStruct struct_type => EStructMember_sem_l (eval_r x) struct_type field ty
        | _ => False_sem
        end
      | _ => False_sem
      end
  | EPoniter_Union_Member x field ty=>
      match expr_type_extract x with
      | TPointer pointed_type =>
        match pointed_type with
        | TUnion union_type => EUnionMember_sem_l (eval_r x) union_type field ty
        | _ => False_sem
        end
      | _ => False_sem
      end
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

Definition SU_state_staysame (s1 s2: state): Prop :=

  s1.(struct_info) = s2.(struct_info) /\
  s1.(union_info) = s2.(union_info) /\
  s1.(type_size) = s2.(type_size).





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
  
  asgn_deref_sem (noSU_var_sem_l X) D1.

Check 12.
(* 定义 int64 序列生成函数 *)
Definition Zseq (start len : Z) : list Z :=
  List.map Z.of_nat (List.seq (Z.to_nat start) (Z.to_nat len)).

Definition declare_sem
             (X: var_name)
             (ty: type): CDenote :=
  {|
    nrm := fun s1 s2 =>
             (*首先原来不能有这个变量名*)
             forall i,
               s1.(env) X <> i /\
              (*使用一块空地址*)
              exists i', 
                (forall pos  ipos var, (In pos (Zseq (Int64.unsigned (s1.(env) var)) (s1.(type_size ) (s1.(type_env) var))))
                                        /\ (In (Int64.unsigned ipos) (Zseq (Int64.unsigned i') (s1.(type_size ) (ty))))
                                        /\ s1.(env) var = ipos 
                                                -> ipos<> Int64.repr pos)
              /\
                s2.(env) X = i' /\
                (s1.(mem) i' <> None) /\
                (forall X', X <> X' -> s1.(env) X' = s2.(env) X') /\
                (forall p, i' <> p -> s1.(mem) p = s2.(mem) p) /\
                (s2.(type_env) X = ty) /\
                SU_state_staysame s1 s2
                ;
    err:= fun s =>exists i, s.(env) X = i;
    inf := ∅;
  |}.


(** 在递归定义的程序语句语义中，只会直接使用表达式用作右值时的值。*)
Inductive com: Type :=
| CSkip : com
| CAsgnVar (X: var_name) (e: expr)
| CAsgnDeref (e1 e2: expr)
| CSeq (c1 c2: com)
| CIf (e: expr) (c1 c2: com)
| CWhile (e: expr) (c: com)
| CDeclare(X: var_name) (ty: type)
| CAsgnBasedOnExp (X: expr) (e: expr) .


Definition False_sem_com: CDenote :=
  {|
    nrm := ∅;
    err := Sets.full;
    inf := ∅;
  |}.

(** 递归定义的程序语句语义。*)
Definition Pointer_Check (e1 :expr) (ty:type): Prop :=
  match expr_type_extract e1 with
  | TPointer ty => True
  | _ => False
  end.
Fixpoint eval_com (c: com): CDenote :=
  match c with
  | CSkip =>
      skip_sem
  | CAsgnVar X e =>
      asgn_var_sem X (eval_r e)
  | CAsgnDeref e1 e2 =>
      match Pointer_Check e1  (expr_type_extract e2) with
      | True => asgn_deref_sem (eval_r e1) (eval_r e2)
      end
  | CSeq c1 c2 =>
      seq_sem (eval_com c1) (eval_com c2)
  | CIf e c1 c2 =>
      if_sem (eval_r e) (eval_com c1) (eval_com c2)
  | CWhile e c1 =>
      while_sem (eval_r e) (eval_com c1)
  | CDeclare X ty =>
      declare_sem X ty
  | CAsgnBasedOnExp X e =>
      asgn_deref_sem (eval_l X) (eval_r e)
  end.









  
  


















