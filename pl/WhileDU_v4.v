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

Module Lang_WhileDU.
Import Lang_WhileD.
Import Lang_While.


Definition type_env: Type := list string.
Definition tag_name: Type :=  string.
Definition men_var_name: Type :=  string.






(* 语法树: C语言类型本身的类型 *)
Inductive type_ins : Type :=
| TInt : type_ins
| TPointer (t: type_ins) : type_ins
| TStruct (x: tag_name) (mvar_list: list men_var) : type_ins
| TUnion (x: tag_name) (mvar_list: list men_var) : type_ins
(* ! 只在匿名结构体声明的时候使用 *)
| TNStruct (mvar_list: list men_var)  : type_ins
| TNUnion (mvar_list: list men_var) : type_ins
with men_var : Type :=
| MVar  (Left_type : type_ins) (var_name:  string) :  men_var.
Check MVar.


(* 语法树:类型定义和声明语句的类型 *)
Inductive type_com : Type :=
| TDecl_struct (x: tag_name) : type_com 
| TDecl_union (x: tag_name)  : type_com 
| TDefine_struct (x: tag_name) (mvar_list: list men_var) : type_com
| TDefine_union (x : tag_name) (mvar_list: list men_var) : type_com.




(* 定义: 成员变量的信息 *)
(* left_type使用 tag_name来存储,因为他有可能是指针,所以如果是多重整数指针就是 ['p','p',...,'p','int'] *)
(* 这里有待思考优化 *)
Record men_var_data := {
  name: men_var_name;
  left_type: list tag_name;
}.



(* 状态相关: 最终存储在type_state中的 type 对应有五种情况，其中struct/union
类型需要存储对应的成员变量信息 list mem_var_data 
*)
Inductive type_data :=
| UnDefined : type_data
| decl_struct  : type_data
| define_struct (mvar_list: list men_var_data) : type_data
| decl_union  : type_data
| define_union (mvar_list: list men_var_data) : type_data.


(* 状态相关：组织当前类型状态 *)
Definition type_state : Type := tag_name ->  type_data.


(* 语义: 类型定义或者定义的指称语义 *)
Record TDenote: Type := {
nrm: type_state -> type_data -> Prop;
err: type_state -> Prop;
}.




Record var: Type := {
  var_name : men_var_name;
  var_type : list tag_name;
}.

Record state: Type := {
  env: var -> option int64;
  mem: int64 -> option val;
}.

(* 辅助函数: 提取某一个成员变量的left_name: type_ins 得到其 list tag_name,
匿名的时候为空列表, 非指针时为单元素列表  
*)
Fixpoint val_left_type_name  (type: type_ins) : (list tag_name ) :=
  match type with
  | TInt => "int" :: nil
  | TPointer (t) =>  "p" :: (val_left_type_name  t)
  | TStruct (x) (mvar_list)  => x:: nil
  | TUnion (x) (mvar_list)  => x :: nil
  | TNStruct (mvar_list)  =>  nil
  | TNUnion (mvar_list)  => nil
end.



(* 辅助函数:输入成员变量的列表 list men_var, 返回对应的 men_var_data的列表 *)
Fixpoint  eval_mem_data_list  (mvarls: list men_var) : ( list men_var_data)  :=
  match mvarls with
  | nil => nil
  | ( MVar (left_type ) (var_name)) :: mvarls_ => (Build_men_var_data (var_name) (val_left_type_name left_type))  ::  (eval_mem_data_list  mvarls_)
end.

Check Build_men_var_data.


(* 指称语义: 声明struct类型 *)
Definition decl_struct_sem (x:tag_name) : TDenote :=
{|
  nrm:= fun ts1 ts2 =>
  (* 如果这个名字没有被定义过, 或者只是被声明过, 那么可以(重复)声明 *)
     ((   ((ts1 x = UnDefined) \/  (ts1 x = (decl_struct)))   /\ (ts2 x = (decl_struct)))  \/ 
  (* 或者找个名字被定义过, 那么保持原状 *)
     (exists mdl, (( ts1 x = define_struct mdl) /\ ( ts2 x = define_struct mdl) )) ) /\
     (* 其他类型名字保持原状 *)
     (forall y, x <> y -> ts2 y = ts1 y );
  err:= fun ts1 =>
  (* 这个类型名被声明或者定义为union类型 *)
     (ts1 x =  decl_union) \/ (exists mdl, ts1 x = define_union mdl);
  
|}.

(* 指称语义: 声明union类型 *)
Definition decl_union_sem (x:tag_name) : TDenote :=
{|
  nrm:= fun ts1 ts2 =>
  (* 如果这个名字没有被定义过, 或者只是被声明过, 那么可以(重复)声明 *)
      ((   ((ts1 x = UnDefined) \/  (ts1 x = (decl_union)))   /\ (ts2 x = (decl_union)))  \/
      (* 或者找个名字被定义过, 那么保持原状 *)
      (exists mdl, ((ts1 x = define_union mdl) /\ ( ts2 x = define_union mdl)) )) /\
       (* 其他类型名字保持原状 *)
      (forall y, x <> y -> ts2 y = ts1 y );
  err:= fun ts1 =>
    (* 这个类型名被声明或者定义为struct类型 *)
      (ts1 x =  decl_struct) \/ (exists mdl, ts1 x = define_struct mdl);
|}.



(* 指称语义: 定义struct类型 *)
Definition define_struct_sem (x: tag_name) (mvar_list: list men_var) : TDenote :=
{|
  nrm:= fun ts1 ts2 =>
  (* 提取出成员变量的信息   *)
     exists mdl,
     ((mdl = eval_mem_data_list mvar_list) 
 (* 如果他没有被定义过，或者只是被声明为struct过，那么他可以被定义struct，把他成员变量的信息都输入到状态里 *)
     /\ ((ts1 x = UnDefined)  \/ (ts1 x = decl_struct))  /\ (ts2 x = (define_struct mdl))) /\
     (* 其他类型名不变 *)
     (forall y, x <> y -> ts2 y = ts1 y );
  err:= fun ts1 =>
  (* 他既不是没有被定义过，又不是被声明为struct *)
     (ts1 x <>  UnDefined ) /\    (ts1 x <>  decl_struct) ;
|}.

(* 指称语义:定义struct类型 *)
Definition define_union_sem (x: tag_name) (mvar_list: list men_var) : TDenote :=
{|
  nrm:= fun ts1 ts2 =>
    (* 提取出成员变量的信息   *)
     exists mdl,
     ((mdl = eval_mem_data_list mvar_list) /\ 
     (* 如果他没有被定义过，或者只是被声明为union过，那么他可以被定义union，把他成员变量的信息都输入到状态里 *)
     ((ts1 x = UnDefined)  \/ (ts1 x = decl_union)) /\ (ts2 x = (define_union mdl))) /\
    (* 其他类型名不变 *)
     (forall y, x <> y -> ts2 y = ts1 y );
  err:= fun ts1 =>
    (* 他既不是没有被定义过，又不是被声明为union *)
     (ts1 x <>  UnDefined )  /\ (ts1 x <> decl_union);
|}.


(* 指称语义:定义空列表的指称语义 *)
Definition Nil_sem: TDenote :=
{|
nrm := Rels.id;
err := ∅;
|}.


(* 辅助函数：定义列表里面的顺序元素的指称语义 *)
Definition tseq_sem (D1 D2: TDenote): TDenote :=
{|
  nrm:= D1.(nrm) ∘ D2.(nrm);
  err:= D1.(err) ∪ (D1.(nrm) ∘ D2.(err));
|}.






Section eval_type_ins_aux.

Variable eval_men_var: men_var -> list type_com.
  
Fixpoint eval_list_men_var (l: list men_var): list type_com :=
    match l with
    | nil => nil
    | cons m0 l0 => eval_men_var m0 ++ eval_list_men_var l0
    end.
  
End eval_type_ins_aux.
  
Fixpoint eval_type_ins (t: type_ins): list type_com :=
  match t with
  | TInt => nil
  | TPointer t0 => eval_type_ins t0
  | TStruct x mvs => TDefine_struct x mvs :: eval_list_men_var eval_men_var mvs
  | TUnion x mvs => TDefine_union x mvs :: eval_list_men_var eval_men_var mvs
  | TNStruct mvs => eval_list_men_var eval_men_var mvs
  | TNUnion mvs => eval_list_men_var eval_men_var mvs
  end
with eval_men_var (mv: men_var): list type_com :=
  match mv with
  | MVar t _ => eval_type_ins t
  end.

(* Definition type_com_to_type_com_list (tc: type_com) : list type_com  :=
  match tc with
  | TDecl_struct X =>    TDecl_struct X :: nil
  | TDecl_union X => TDecl_union X  :: nil
  | TDefine_struct X  mvar_list =>  (TDefine_struct X   mvar_list )::  (((eval_list_men_var   eval_men_var )mvar_list)) 
  | TDefine_union X  mvar_list =>   TDefine_union X  mvar_list  ::  (( eval_list_men_var eval_men_var mvar_list) )
end. *)

Section extend_type_com_aux.

Variable extend_type_com: type_com -> list type_com.
  
Fixpoint extend_list_type_com (l: list type_com ): list type_com :=
    match l with
    | nil => nil
    | cons m0 l0 => extend_type_com m0 ++  extend_list_type_com l0
    end.
  
End extend_type_com_aux.


Definition extend_type_com (tc: type_com) :  list type_com :=
  match tc with
  | TDecl_struct X =>  TDecl_struct X  :: nil
  | TDecl_union X =>  TDecl_struct X :: nil
  | TDefine_struct X  mvar_list =>     (TDefine_struct X  mvar_list)  ::  ((eval_list_men_var eval_men_var mvar_list)) 
  | TDefine_union X  mvar_list =>   (TDefine_union X  mvar_list) ::   (( eval_list_men_var eval_men_var mvar_list) )
  end .



  


Fixpoint eval_type_com_list (tcls: list  type_com) : TDenote :=
  (* let evtend_tcls =  *) 
  match tcls with
  | nil => Nil_sem
  | TDecl_struct X :: tcls0 => tseq_sem ( decl_struct_sem ( X))  ( eval_type_com_list tcls0)
  | TDecl_union X :: tcls0 => tseq_sem ( decl_union_sem ( X)) ( eval_type_com_list tcls0)
  | TDefine_struct X  mvar_list :: tcls0 =>   tseq_sem (define_struct_sem X  mvar_list) (eval_type_com_list tcls0 )
  | TDefine_union X  mvar_list :: tcls0 =>   tseq_sem ( define_union_sem  X  mvar_list) (eval_type_com_list tcls0 )
  end.


(* 指称语义: type_com *)
Definition overall_tsem_nrm (tcls: list type_com) : TDenote :=
  eval_type_com_list  ((extend_list_type_com extend_type_com tcls) ).



  

End Lang_WhileDU.


  (* ----------------我是分割线--------------------------- *)


  
(* 
  `

  Section eval_type_com_aux.

  Variable eval_type_com: type_com -> TDenote.
    
  Fixpoint eval_list_type_com (l: list type_com ): TDenote :=
      match l with
      | nil => Nil_sem
      | cons m0 l0 => tseq_sem  (eval_type_com m0)    (eval_list_type_com l0)
      end.
    
  End eval_type_com_aux.
  
  Fixpoint eval_type_com (tc: type_com)  :TDenote :=
    match tc with
    | TDecl_struct X =>  decl_struct_sem X 
    | TDecl_union X =>  decl_union_sem X 
    | TDefine_struct X  mvar_list =>  tseq_sem   (define_struct_sem X mvar_list) ( (eval_list_type_com   eval_type_com)   )
    | TDefine_union X  mvar_list =>  tseq_sem  (define_union_sem X mvar_list) ((eval_list_type_com  eval_type_com)    )
    end .
  

Section trans_aux.


Definition eval_type_com_list (tc: type_com) : list type_com :=
  match tc with
  | TDecl_struct x => decl_struct_sem



Section getD_aux.

  (* 声明变量: 其实是一个函数，把var memb 里面对应的类型 type ins 变化为等价的定义类型的语句列表 *)
Variable eval_type_com : type_com ->  TDenote .





(* 辅助函数: 把var memb 列表 里面对应的类型 type ins 变化为等价的定义类型的语句列表 *)
Fixpoint eval_type_com_list (tcls: list type_com) : list type_com  :=
  match tcls with
  | nil => Nil_sem
  | cons tc1 tcls0 =>  tseq_sem (eval_type_com tc1)  (eval_type_com_list tcls0)
  end.
  
End getD_aux.



Fixpoint eval_type_com (tc: type_com) : TDenote :=
match tc with
| TDecl_struct X =>  decl_struct_sem X 
| TDecl_union X =>  decl_union_sem X 
| TDefine_struct X  mvar_list =>  tseq_sem   (define_struct_sem X mvar_list) ( (eval_type_com_list   eval_type_com)  ((eval_list_men_var eval_men_var mvar_list)) )
| TDefine_union X  mvar_list =>  tseq_sem  (define_union_sem X mvar_list) ((eval_type_com_list  eval_type_com)  (( eval_list_men_var eval_men_var mvar_list) ))
end .

 *)
