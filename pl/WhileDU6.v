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

Definition var_name: Type := string.

Module Lang_WhileDU6.
Import Lang_WhileD.
Import Lang_While.

Inductive type : Type :=
| TInt : type
| TPointer (t: type) : type
| TStruct (x: string) : type
| TUnion (x: string) : type
with men_var : Type :=
| MVar  (men_type : type) (var_name:  string) :  men_var.

Inductive expr_type : Type :=
| EConst (n: Z) (ty : type) : expr_type
| EVar (x: var_name) (ty:type): expr_type
| EBinop (op: binop) (e1 e2: expr_type)(ty:type) : expr_type
| EUnop (op: unop) (e: expr_type)(ty:type) : expr_type
| EDeref (e: expr_type)(ty:type) : expr_type
| EAddrOf (e: expr_type) (ty:type): expr_type
(*| ECast (e: expr_type) (t: type) : expr_type   Type casting *)
| EStructMember (x:expr_type) (field: var_name) (ty:type): expr_type  (* Access struct member *)
| EUnionMember (x:expr_type) (field: var_name)(ty:type) : expr_type  (* Access union member *)
| EPoniter_Struct_Member (x:expr_type) (field: var_name)(ty:type) : expr_type  (* Access poniter member *)
| EPoniter_Union_Member (x:expr_type) (field: var_name)(ty:type) : expr_type  (* Access poniter member *).

(*把类型环境拆出去*)
Record state: Type := {
  env: var_name -> int64;
  mem: int64 -> option val;
  type_env : var_name -> type;
}.

Notation "s '.(env)'" := (env s) (at level 1).
Notation "s '.(mem)'" := (mem s) (at level 1).

Record type_env_state: Type := {
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


Module EDenote_type.

Record EDenote_type: Type := {
  type_nrm: type_env_state->state -> int64 -> Prop;
  type_err: type_env_state->state -> Prop;
}.

End EDenote_type.

Import EDenote_type.

Notation "x '.(type_nrm)'" := (EDenote_type.type_nrm x)
  (at level 1, only printing).

Notation "x '.(type_err)'" := (EDenote_type.type_err x)
  (at level 1, only printing).

Ltac any_nrm x := exact (EDenote_type.type_nrm x).

Ltac any_err x := exact (EDenote_type.type_err x).

Notation "x '.(type_nrm)'" := (ltac:(any_nrm x))
  (at level 1, only parsing).

Notation "x '.(type_err)'" := (ltac:(any_err x))
  (at level 1, only parsing).


  Definition NotStructOrUnion (ty1 ty2:type): Prop := 
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

Definition arith_sem1 Zfun (D1 D2: EDenote_type): EDenote_type :=
{|
type_nrm := fun t  =>  (arith_sem1_nrm Zfun (D1.(type_nrm) t) (D2.(type_nrm) t));
type_err := fun t  => arith_sem1_err Zfun (D1.(type_nrm) t) (D2.(type_nrm) t) ;
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

Definition arith_sem2 int64fun (D1 D2: EDenote_type): EDenote_type :=
  {|
    type_nrm := fun t =>arith_sem2_nrm int64fun (D1.(type_nrm) t) (D2.(type_nrm) t);
    type_err := fun t => D1.(type_err) t ∪ D2.(type_err) t ∪
           arith_sem2_err (D1.(type_nrm) t) (D2.(type_nrm) t);
  |}.


Definition cmp_sem_nrm
(c: comparison)
(D1 D2: state -> int64 -> Prop)
(s: state)
(i: int64): Prop :=
exists i1 i2,
D1 s i1 /\ D2 s i2 /\ cmp_compute_nrm c i1 i2 i.

Definition cmp_sem c (D1 D2: EDenote_type): EDenote_type :=
{|
type_nrm := fun t  =>  (cmp_sem_nrm c (D1.(type_nrm) t) (D2.(type_nrm) t) );
type_err := fun t  => (D1.(type_err) t ) ∪ (D2.(type_err) t );
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
  

Definition neg_sem (D1: EDenote_type): EDenote_type :=
  {|
    type_err := fun t => ((D1.(type_err) t) ∪ neg_sem_err ( ( D1.(type_nrm) t ) )) ;
    type_nrm := fun t =>neg_sem_nrm (D1.(type_nrm) t);
  |}.


  Definition not_sem_nrm
  (D1: state -> int64 -> Prop)
  (s: state)
  (i: int64): Prop :=
exists i1, D1 s i1 /\ not_compute_nrm i1 i.

Definition not_sem (D1: EDenote_type): EDenote_type :=
{|
type_nrm := fun t => not_sem_nrm (D1.(type_nrm) t);
type_err := fun t => D1.(type_err) t;
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

Definition and_sem (D1 D2: EDenote_type): EDenote_type :=
{|
type_nrm :=fun t =>  and_sem_nrm ( D1.(type_nrm) t) (D2.(type_nrm) t);
type_err := fun t => (D1.(type_err) t )∪ and_sem_err (D1.(type_nrm) t) (D2.(type_err) t);
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

Definition or_sem (D1 D2: EDenote_type) : EDenote_type :=
{|
type_nrm := fun t => or_sem_nrm (D1.(type_nrm) t)( D2.(type_nrm) t );
type_err := fun t => D1.(type_err) t ∪ or_sem_err (D1.(type_nrm) t) ( D2.(type_err) t);
|}.

Definition unop_sem (op: unop) (D: EDenote_type): EDenote_type :=
match op with
| ONeg =>  D
| ONot => not_sem D
end.

Definition binop_sem (op: binop) (D1 D2: EDenote_type) : EDenote_type :=
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

Definition const_sem (n: Z) : EDenote_type :=
    {|
      type_nrm := fun t s i =>
               i = Int64.repr n /\
               Int64.min_signed <= n <= Int64.max_signed ;
      type_err := fun t s =>
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

Definition deref_sem_r (D1: EDenote_type): EDenote_type :=
        {|
        type_nrm := fun t => deref_sem_nrm (D1.(type_nrm) t);
        type_err := fun t => D1.(type_err) t ∪ (deref_sem_err (D1.(type_nrm) t));
        |}.
   

Definition var_sem_l (X: var_name): EDenote_type :=
        {|
        type_nrm := fun t s i => s.(env) X = i;
        type_err := ∅;
        |}.

Definition var_sem_r (X: var_name) (ty : type) : EDenote_type :=
        {|
            type_nrm := (fun t s i => s.(type_env) X = ty) ∩ (deref_sem_r (var_sem_l X)).(type_nrm);
            type_err := (fun t s  => s.(type_env) X <> ty) ∪ (deref_sem_r (var_sem_l X)).(type_err);
        |}.
          
Definition False_sem: EDenote_type :=
    {|
    type_nrm := ∅;
    type_err := Sets.full;
    |}.

(*辅助函数：查找结构体中某个字段的类型*)
Fixpoint calculate_type  (field:string)(fields:list men_var) : option type := 
  match fields with
  | [] => None
  | MVar ty f :: rest =>
    if string_dec f field
    then Some ty
    else calculate_type  field rest
  end.

  (* 辅助函数：计算结构体中字段的偏移量 *)
Fixpoint calculate_offset (t:type_env_state) (field: string) (fields: list men_var) (offset: Z) : option Z :=
    match fields with
    | [] => None (* 未找到字段，返回 None *)
    | MVar ty f :: rest =>
      if string_dec f field
      then Some offset (* 找到字段，返回当前偏移量 *)
      else calculate_offset t field rest (offset + t.(type_size) ty ) (* 继续查找下一个字段 *)
    end.


    (* 辅助函数：查找结构体中字段的偏移量 *)
Definition find_field_offset (t : type_env_state) (field: string) (struct_fields: list men_var) : option Z :=
    calculate_offset t field struct_fields (0).

    Definition noSU_var_sem_l (X: var_name): EDenote_type :=
{|
type_nrm := fun t s i => s.(env) X = i /\ (s.(type_env) X) <> TStruct X /\ (s.(type_env) X) <> TUnion X;
type_err := ∅;
|}.
Definition EStructMember_sem_l (D1: EDenote_type) (struct_type: string) (field: string) (ty:type) : EDenote_type :=
{|
    type_nrm := (fun t s i => exists i' , (D1.(type_nrm) t s i' )/\ (
                                match find_field_offset t field (t.(struct_info) struct_type) with
                                (*查一下这个字段field在D1对应的struct Type里的偏移量*)
                                | Some offset => i = Int64.add i' (Int64.repr offset)
                                | None => False
                                end) /\ calculate_type  field (t.(struct_info) struct_type) = Some ty
                                    );
    type_err := fun t => D1.(type_err) t ∪ (fun s => exists i', (D1.(type_nrm) t s i') /\ 
                                (
                                match find_field_offset t  field (t.(struct_info) struct_type) with
                                | Some offset => False
                                | None => True
                                end
                                \/ calculate_type field (t.(struct_info) struct_type) = None
                                )
                    );
|}.


Definition EUnionMember_sem_l (D1: EDenote_type) (union_type: string) (field: string) (ty:type): EDenote_type :=
    {|
    type_nrm := (fun t s i => exists i' , (D1.(type_nrm) t s i' )/\ (
                                    match find_field_offset t field (t.(union_info) union_type) with
                                    (*查一下这个字段field在D1对应的union Type里的"偏移"量*)
                                    | Some offset => i =  i' 
                                    | None => False
                                    end) /\ calculate_type  field (t.(union_info) union_type) = Some ty
                                    );
    type_err := fun t => D1.(type_err) t ∪ (fun s => exists i', (D1.(type_nrm) t s i') /\ (
                                    match find_field_offset t field ( (t.(union_info) union_type)) with
                                    | Some offset => False
                                    | None => True
                                    end 
                                    \/ calculate_type field (t.(union_info) union_type) = None
                                    ));
    |}. 


Definition struct_member_sem_r (x:EDenote_type) (struct_type: string)(field:string)(ty:type): EDenote_type :=
    {|
        type_nrm :=  fun t s i => exists i', (x.(type_nrm) t s i') /\ (
                                                    match find_field_offset t field (t.(struct_info) struct_type) with
                                                    (*查一下这个字段field在x对应的struct Type里的偏移量*)
                                                    None => False
                                                    | Some offset => s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vint i)
                                                    end  /\ calculate_type  field (t.(struct_info) struct_type) = Some ty);
        type_err := fun t=>x.(type_err) t ∪ (fun s => exists i', (x.(type_nrm) t s i') /\ (
                                                    match find_field_offset t field (t.(struct_info) struct_type) with
                                                    | None => True
                                                    | Some offset => s.(mem) (Int64.add i' (Int64.repr offset)) = None \/ s.(mem) (Int64.add i' (Int64.repr offset)) = Some (Vuninit)
                                                    end 
                                                    \/ calculate_type field (t.(struct_info) struct_type) = None
                                                    ));
    |}.
    
    Definition union_member_sem_r (x:EDenote_type) (union_type: string)(field:string)(ty:type): EDenote_type :=
    {|
        type_nrm :=  fun t s i => exists i', (x.(type_nrm) t s i') /\ (
                                                    match find_field_offset t field (t.(union_info) union_type) with
                                                    (*查一下这个字段field在x对应的union Type里的"偏移"量*)
                                                    None => False
                                                    | Some offset => s.(mem) i' = Some (Vint i)
                                                    end  /\ calculate_type  field (t.(union_info) union_type) = Some ty);
        type_err := fun t=> x.(type_err) t  ∪ (fun s => exists i', (x.(type_nrm) t s i') /\ (
                                                    match find_field_offset t field (t.(union_info) union_type) with
                                                    | None => True
                                                    | Some offset => s.(mem) i' = None \/ s.(mem) i' = Some (Vuninit)
                                                    end ));
    
    
    |}.

Definition expr_type_extract (e:expr_type): type :=
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

      


    

    Fixpoint eval_r (e: expr_type): EDenote_type :=
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
        with eval_l (e: expr_type): EDenote_type :=
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
            {| type_nrm := ∅; type_err := Sets.full; |}
        end.





Definition test_true (D: EDenote_type):
        type_env_state -> state -> state -> Prop :=
        fun t =>
          Rels.test
            (fun s  =>
              exists i , D.(type_nrm) t s i /\ Int64.signed i <> 0).



Definition test_false  (D: EDenote_type):
    type_env_state->state -> state -> Prop := fun t=>
          Rels.test (fun s =>  D.(type_nrm) t s (Int64.repr 0)).
Module CDenote_type.

Record CDenote_type: Type := {
          type_nrm:  type_env_state->state-> state -> Prop ;
          type_err:  type_env_state->state -> Prop;
          type_inf:  type_env_state->state -> Prop
        }.        
End CDenote_type. 
Import CDenote_type.
Definition SU_state_staysame (s1 s2: type_env_state): Prop :=

  s1.(struct_info) = s2.(struct_info) /\
  s1.(union_info) = s2.(union_info) /\
  s1.(type_size) = s2.(type_size).


Notation "x '.(nrm)'" := (CDenote_type.type_nrm x)
  (at level 1, only printing).

Notation "x '.(err)'" := (CDenote_type.type_err x)
  (at level 1, only printing).

Ltac any_nrm x ::=
  match type of x with
  | EDenote_type => exact (EDenote_type.type_nrm x)
  | CDenote_type => exact (CDenote_type.type_nrm x)
  end.

Ltac any_err x ::=
  match type of x with
  | EDenote_type => exact (EDenote_type.type_err x)
  | CDenote_type => exact (CDenote_type.type_err x)
  end.

Definition skip_sem: CDenote_type :=
  {|
    type_nrm := fun t=>Rels.id;
    type_err := ∅;
    type_inf := ∅;
  |}.

Definition seq_sem (D1 D2: CDenote_type): CDenote_type :=
  {|
    type_nrm :=fun t=> (D1.(type_nrm) t )∘ (D2.(type_nrm) t);
    type_err := fun t=>D1.(type_err) t ∪ (D1.(type_nrm) t ∘ (D2.(type_err) t));
    type_inf :=fun t=> D1.(type_inf) t ∪ ((D1.(type_nrm) t)∘( D2.(type_inf) t));
  |}.

Definition if_sem
             (D0: EDenote_type)
             (D1 D2: CDenote_type): CDenote_type :=
  {|
    type_nrm:= fun t=>
            ( (test_true  D0 t)  ∘ (D1.(type_nrm) t)) ∪
           ( (test_false  D0 t) ∘ (D2.(type_nrm) t));
    type_err := fun t=> 
            (D0.(type_err) t) ∪
           ((test_true  D0 t) ∘ (D1.(type_err) t)) ∪
           ((test_false  D0 t )∘ (D2.(type_err) t));
    type_inf := fun t=> 
            ((test_true  D0 t) ∘ (D1.(type_inf) t)) ∪
           ((test_false  D0 t) ∘ (D2.(type_inf) t))
  |}.

Fixpoint boundedLB_nrm
          (t: type_env_state)
           (D0: EDenote_type)
           (D1: CDenote_type)
           (n: nat):
   state -> state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
      ((test_true D0 t ) ∘ (D1.(type_nrm) t) ∘ boundedLB_nrm t D0 D1 n0) ∪
      (test_false D0 t)
  end.

Fixpoint boundedLB_err
            (t: type_env_state)
           (D0: EDenote_type)
           (D1: CDenote_type)
           (n: nat): state -> Prop :=
  match n with
  | O => ∅
  | S n0 =>
     (test_true D0 t∘
        ((D1.(type_nrm) t ∘ boundedLB_err t D0 D1 n0) ∪
         D1.(type_err) t)) ∪
      D0.(type_err) t
  end.

Definition is_inf
              (t: type_env_state)
             (D0: EDenote_type)
             (D1: CDenote_type)
             (X: state -> Prop): Prop :=
  X ⊆ test_true D0 t ∘ (((D1.(type_nrm) t) ∘ X) ∪ D1.(type_inf) t).

Definition while_sem
             (D0: EDenote_type)
             (D1: CDenote_type): CDenote_type :=
  {|
    type_nrm := fun t=>⋃ (boundedLB_nrm t D0 D1);
    type_err := fun t =>⋃ (boundedLB_err t D0 D1);
    type_inf := fun t =>Sets.general_union (is_inf t D0 D1);
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
             (D1 D2: EDenote_type): CDenote_type :=
  {|
    type_nrm := fun t=>(asgn_deref_sem_nrm (D1.(type_nrm) t) (D2.(type_nrm) t));
    type_err := fun t=> D1.(type_err)  t ∪ D2.(type_err) t ∪
           asgn_deref_sem_err (D2.(type_nrm) t);
    type_inf := ∅;
  |}.

(** 变量赋值的行为可以基于此定义。*)





Definition asgn_var_sem
             (X: var_name)
             (D1: EDenote_type): CDenote_type :=
  
  asgn_deref_sem (noSU_var_sem_l X) D1.

Check 12.
(* 定义 int64 序列生成函数 *)
Definition Zseq (start len : Z) : list Z :=
  List.map Z.of_nat (List.seq (Z.to_nat start) (Z.to_nat len)).

Definition declare_sem
             (X: var_name)
             (ty: type): CDenote_type :=
  {|
    type_nrm := fun t s1 s2 =>
             (*首先原来不能有这个变量名*)
             forall i,
               s1.(env) X <> i /\
              (*使用一块空地址*)
              exists i', 
                (forall pos  ipos var, (In pos (Zseq (Int64.unsigned (s1.(env) var)) (t.(type_size ) (s1.(type_env) var))))
                                        /\ (In (Int64.unsigned ipos) (Zseq (Int64.unsigned i') (t.(type_size ) (ty))))
                                        /\ s1.(env) var = ipos 
                                                -> ipos<> Int64.repr pos)
              /\
                s2.(env) X = i' /\
                (s1.(mem) i' <> None) /\
                (forall X', X <> X' -> s1.(env) X' = s2.(env) X') /\
                (forall p, i' <> p -> s1.(mem) p = s2.(mem) p) /\
                (s2.(type_env) X = ty) 
                ;
                type_err:= fun t s =>exists i, s.(env) X = i;
                type_inf := ∅;
  |}.


(** 在递归定义的程序语句语义中，只会直接使用表达式用作右值时的值。*)
Inductive com: Type :=
| CSkip : com
| CAsgnVar (X: var_name) (e: expr_type)
| CAsgnDeref (e1 e2: expr_type)
| CSeq (c1 c2: com)
| CIf (e: expr_type) (c1 c2: com)
| CWhile (e: expr_type) (c: com)
| CDeclare(X: var_name) (ty: type)
| CAsgnBasedOnExp (X: expr_type) (e: expr_type) .


Definition False_sem_com: CDenote_type :=
  {|
    type_nrm := ∅;
    type_err := Sets.full;
    type_inf := ∅;
  |}.

(** 递归定义的程序语句语义。*)
Definition Pointer_Check (e1 :expr_type) (ty:type): Prop :=
  match expr_type_extract e1 with
  | TPointer ty => True
  | _ => False
  end.
Fixpoint eval_com (c: com): CDenote_type :=
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


End Lang_WhileDU6.

Module Lang_WhileD_Malloc.











  
  

















