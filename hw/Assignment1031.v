Require Import Coq.Classes.RelationClasses.
Require Import PL.DenotationalSemantics.
Require Import PL.PracticalDenotations.
Import BWFix KTFix.
Local Open Scope order_scope.

(************)
(** 习题：  *)
(************)


(** 请证明下面关于Knaster-Tarski最大不动点的性质。 *)

Lemma KT_GFix_mono:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f g: A -> A),
    mono f ->
    mono g ->
    (forall a, f a <= g a) ->
    KT_GFix f <= KT_GFix g.
Proof.
simpl.
intros.
unfold KT_GFix.

apply lub_tight; unfold is_ub; intros.
transitivity (f a').
+tauto.
+  pose proof H1 a'.
apply lub_sound.

  transitivity (g a').
- tauto.
-tauto.
-apply H0.
tauto.
Qed.




(************)
(** 习题：  *)
(************)


(** 很显然，任意完备格上都有最小元，它可以被定义为空集的上确界。*)

Definition bot
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}: A :=
  lub (fun _ => False).

(** 下面请你证明，空集的上确界确实是最小元。*)
Lemma bot_is_least
        {A: Type}
        `{CLA: CompleteLattice_Setoid A}:
  forall a: A, bot <= a.
Proof.
intros.
unfold bot.
apply lub_tight.
unfold is_ub.
intros.
tauto.
Qed.

(************)
(** 习题：  *)
(************)


(** 我们已经学过，在完备偏序集上，单调连续函数_[f]_的最小不动点可以定义为   

        _[bot]_, _[f bot]_, _[f (f bot)]_, ...   

    的上确界。那么在完备格上，如果_[f]_是一个单调函数，上面这个计算结果是不动点吗？下面
    是这一计算结果的Coq定义*)

Definition BW
             {A: Type}
             `{CLA: CompleteLattice_Setoid A}
             (f: A -> A) :=
  lub (fun a => exists n: nat, a = Nat.iter n f bot).

(** 请你证明以下结论。*)

Lemma CL_mono_KT:
  forall
    {A: Type}
    `{CLA: CompleteLattice_Setoid A}
    {EquivA: Equivalence equiv}
    (f: A -> A),
    mono f ->
    BW f <= KT_GFix f.
Proof.
simpl.
intros.

unfold BW .
apply lub_tight.
unfold is_ub.
intros.
apply lub_sound.
destruct H0.
  assert (forall n, Nat.iter n f bot <= Nat.iter (S n) f bot).
  { 
    intros.
    induction n.
    - simpl.
       apply bot_is_least.
    - simpl.
        simpl in IHn.
        apply H.
        tauto.    
  }
  specialize (H1 x).
  rewrite H0.
tauto.
Qed.




