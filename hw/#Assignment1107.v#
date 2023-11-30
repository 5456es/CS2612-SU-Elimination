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

intros.
split.
+simpl.
 apply Rels_concat_id_r. 
+simpl.
sets_unfold.
intros.
split.
-intros.
destruct  H.
*tauto.
*destruct H .
tauto.
-intros.
left;tauto.
+simpl.
sets_unfold.
intros.
split.
-intros.
destruct H.
*tauto.
*destruct H.
tauto.
-intros.
left ; tauto.
Qed.





(************)
(** 习题：  *)
(************)


(** 请证明语义等价。*)

Theorem CSkip_CSeq: forall c,
  [[ skip; c ]] ~=~ c.

Proof.

intros.
split.
+simpl.
 apply Rels_concat_id_l. 
+simpl.
sets_unfold.
intros.
split.
-intros.
destruct  H.
*tauto.
*destruct H .
destruct H.
rewrite <-H in H0.
tauto.
-intros.
right.
exists a.



tauto.

+simpl.
sets_unfold.
intros.
split.
-intros.
destruct H.
*tauto.
*destruct H.
destruct H.
rewrite <- H in H0.

tauto.
-intros.

right.
exists a.

 tauto.
Qed.
