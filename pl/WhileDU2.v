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


Definition struct_type_name := string.
Definition union_type_name := string.
Definition var_name := string.
Definition fieldname := string.
Definition union_case_name := string.
Definition SU_type_name := string.

Module Type_defined.
Import Lang_WhileD.
Import Lang_While.
Inductive type : Type :=
  | TInt : type
  | TBool : type
  | TIntPtr : type->type
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
  Definition struct_union_table : Type := list (type * option struct_info * option union_info).

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








  Check empty_env.
  Check add_struct_type "a" [StructField "b" TInt; StructField "c" TInt] empty_env.
  Check add_union_type "a" [UnionCase "b" TInt None; UnionCase "c" TInt None] empty_env.
  Compute add_struct_type "a" [StructField "b" TInt; StructField "c" TInt] empty_env.
  Compute add_union_type "a" [UnionCase "b" TInt None; UnionCase "c" TInt None] empty_env.
  Compute add_union_type "a" [UnionCase "b" TInt None; UnionCase "c" TInt None]
  (add_union_type "x" [UnionCase "y" TBool None; UnionCase "z" TInt (Some (EConst 42))]
     empty_env).
  Compute add_struct_type "a" [StructField "b" TInt; StructField "c" TInt]
     (add_union_type "x" [UnionCase "y" TBool None; UnionCase "z" TInt (Some (EConst 42))]
        empty_env).


(*
Fixpoint lookup_field_type (field: var_name) (fields: list struct_field): option type :=
  match fields with
  | [] => None
  | StructField x fieldType :: rest => if string_dec field x then Some fieldType else lookup_field_type field rest
  end.


Compute lookup_field_type "x" [StructField "x" TInt; StructField "y" TBool].

Fixpoint lookup_union_case_type (case: var_name) (cases: list union_case): option type :=
  match cases with
  | [] => None
  | UnionCase x fieldType _ :: rest => if string_dec case x then Some fieldType else lookup_union_case_type case rest
  end.

Compute lookup_union_case_type "x" [UnionCase "x" TInt None; UnionCase "y" TBool None].*)
Check (TStruct "a").
(*待续**)
End SU_Env.

Module WhileDU.

Import Lang_WhileD.
Import Lang_While.
Import Type_defined.
Import SU_Env.

Inductive expr : Type :=
  | EConst (n: Z): expr
  | EVar (x: var_name): expr
  | EAdd (e1 e2: expr): expr
  | ESub (e1 e2: expr): expr
  | EMul (e1 e2: expr): expr
  | EInt (e: expr): expr
  | EPtrDeref (e: expr): expr
  | EStructField (Struct: expr) (field: fieldname): expr
  | EUnionCaseField (Union: expr) (case: union_case_name ): expr
  | EStruct (structType: struct_type_name) (fields: list (fieldname * expr)): expr
  | EUnion (unionType: union_type_name) (case: var_name) (e: expr): expr.


Inductive com : Type :=
  | CSkip: com
  | CDecl (x: var_name) (t: type): com
  | CAsgn (x: var_name) (e: expr): com
  | CStructAsgn (x: var_name) (fields: list struct_field): com
  | CUnionAsgn (x: var_name) (cases: list union_case): com
  | CSeq (c1 c2: com): com
  | CIf (e: expr) (c1 c2: com): com
  | CWhile (e: expr) (c: com): com.

 





