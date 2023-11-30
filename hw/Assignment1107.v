Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import SetsClass.SetsClass. Import SetsNotation.
Require Import PL.SyntaxInCoq.
Require Import PL.DenotationalSemantics.
Require Import PL.PracticalDenotations.
Require Import PL.EquivAndRefine.
Import Lang_While DntSem_While1 DntSem_While2.
Import EDenote CDenote.
Local Open Scope sets.

(************)
(** 习题：  *)
(************)


(** 请证明语义等价。*)

Theorem CSeq_CSkip: forall c,
  [[ c; skip ]] ~=~ c.
Proof.
  assert (forall (A: Type) (B: A -> A -> Prop), B ∘ ∅ == ∅).
  {
    intros.
    sets_unfold.
    intros.
    split.
    - intros. destruct H. destruct H. tauto.
    - tauto.   
  }
  intros.
  split.
  - simpl.
    apply Rels_concat_id_r. 
  - simpl.
    rewrite (H _ _).
    apply Sets_union_empty.
  - simpl.
    rewrite (H _ _).
    apply Sets_union_empty.
Qed.


(************)
(** 习题：  *)
(************)


(** 请证明语义等价。*)

Theorem CSkip_CSeq: forall c,
  [[ skip; c ]] ~=~ c.

Proof.
  assert (forall x: state -> Prop,  ∅ ∪ x == x).
  {
    intros.
    sets_unfold.
    intros.
    split.
    - intros. destruct H. tauto. tauto.
    - tauto.   
  }
  intros.
  split.
  - simpl.
    apply Rels_concat_id_l. 
  - simpl.
    rewrite Rels_concat_id_l. 
    apply H.
  - simpl.
    rewrite Rels_concat_id_l. 
    apply H.
Qed.