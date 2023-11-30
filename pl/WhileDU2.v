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
  | TStruct : struct_type_name ->list struct_field-> type
  | TUnion : union_type_name -> list union_case->type
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

Definition type_env : Type := list (var_name * (type * option struct_info * option union_info)).

Definition empty_env : type_env := nil.

  Definition add_SU_type (x: SU_type_name) (t: type) (sinfo: option struct_info) (uinfo: option union_info) (env: type_env): type_env :=
    (x, (t, sinfo, uinfo)) :: env.
  

  Definition add_struct_type (structName: var_name) (fields: list struct_field) (env: type_env): type_env :=
  add_SU_type structName (TStruct structName fields) (Some (StructDef structName fields)) None env.

  Definition add_union_type (unionName: var_name) (cases: list union_case) (env: type_env): type_env :=
  add_SU_type unionName (TUnion unionName cases) None (Some (UnionDef unionName cases)) env.


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

 





