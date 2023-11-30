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

(*关于这个任务*)

Definition StructName: Type := string.
Definition UnionName: Type := string.
Definition Member_name: Type := string.




(*首先定义我们预期讨论的涉及【类型】,这里我们
  考虑int pointer struct union
  Int可以解释自己
  Pointer需要指示【类型】
  Struct和Union需要指示【SU名字】和【成员】
    其中成员是一个list，每个成员是一个pair，包含【成员名字】和【类型】
  *)
Inductive type : Type :=
  | Int : type
  | Pointer : type -> type
  | Struct : StructName -> SU_Field -> type
  | Union : UnionName -> SU_Field -> type
with SU_Field : Type :=
  | SUField : list (Member_name * type) -> SU_Field.





Inductive type_data :=
| Struct_data (var_list: list (string * type)) : type_data
| Union_data  (var_list: list (string * type)) : type_data
| Int_data : int64 -> type_data
| Pointer_data : int64 -> type_data
| Null_data : type_data.



(*然后我们尝试定义语句
定义struct和union的时候，我们需要指定【SU名字】和【成员】 比如定义Day[温度，天气]
声明的时候，我们需要指定【SU名字】和实例名字 比如声明Monday 需要表面Day Monday  
*)




Inductive type_cmd: Type :=
| TDefine_struct (x: StructName) (var_list: list (string * type)) : type_cmd  (*定义结构体*)
| TDefine_union (x: UnionName) (var_list: list (string * type)) : type_cmd  (*定义联合体*)
| TDecl_struct (x: StructName) (instance:string): type_cmd  (*声明结构体*)
| TDecl_union (x: UnionName) (instance:string): type_cmd (*声明联合体*)

| TDecl_int (x: string) : type_cmd  (*声明int*)
| TDecl_pointer (x: string) : type_cmd  (*声明指针*)

| TInt_assign (x: string) (n: int64) : type_cmd  (*int赋值*)
| TPointer_assign (x: string) (y: string) : type_cmd  (*指针赋值*)
| TStruct_membervar_assign (Instance_name: string) (member: type) (data:type_data) : type_cmd  (*结构体内容赋值*)
| TUnion_membervar_assign (Instance_name: string) (member: type) (data:type_data) : type_cmd.  (*联合体内容赋值*)




(*
1.var和const是不是也要并入类型？
2.var是不是不放在内存上？
3.
*)

(*接下来我们定义对【类型】内容的 state，eval，expression进行定义*)



Record var : Type := {
  var_name: string;
  var_type: type;
}.


Record type_state : Type := {
(*
  env: var ->  int64; (* environment is a total map from variables to values *)
  mem: int64 -> option val; (* memory is a partial map from addresses to values *)
*)
env: var ->  int64;
mem: int64 -> option val;
}.


Inductive type_data :=
| Struct_data (var_list: list (string * type)) : type_data
| Union_data  (var_list: list (string * type)) : type_data
| Int_data : int64 -> type_data
| Pointer_data : int64 -> type_data
| Null_data : type_data.






Record TDenote: Type := {
nrm: type_state -> type_data -> Prop;
err: type_state -> Prop;
}.








(*然后我们尝试定义表达式*)


(*// 定义一个单层非匿名结构体
struct Person {
    int age;
    int* height;  // 指针字段
};

// 定义一个单层非匿名联合体
union Data {
    int intValue;
    int* intPointer;  // 指针字段
};

// 在结构体中使用结构体字段和指针字段
struct Company {
    struct Person employee;  // 结构体字段
    struct Person* manager;  // 指针字段
};

// 在联合体中使用结构体和联合体字段
union MixedData {
    struct Person personData;  // 结构体字段
    union Data unionData;      // 联合体字段
};
*)

Check (Struct "Person" (SUField [("age", Int); ("height", Pointer Int)])).

(*然后我们定义类型系统有关的Cmd，我们这里暂时只考虑SU的定义和声明*)
Inductive type_cmd: Type :=
| TDefine_struct (x: StructName) (var_list: list (string * type)) : type_cmd
| TDefine_union (x: UnionName) (var_list: list (string * type)) : type_cmd
| TDecl_struct (x: StructName) : type_cmd
| TDecl_union (x: UnionName) : type_cmd.
(*此处不考虑初始化的时候设置SU类型内部参数*)



Inductive type_data :=
| Struct_data (var_list: list (string * type)) : type_data
| Union_data  (var_list: list (string * type)) : type_data
| Null_data : type_data.




Definition type_state : Type := string ->  type_data.

Record TDenote: Type := {
nrm: type_state -> type_data -> Prop;
err: type_state -> Prop;
}.













