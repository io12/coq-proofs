Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Mult.
Require Import Coq.Numbers.Natural.Abstract.NDiv.

(** 1 + 2 + ... + n *)
Fixpoint sum_1_to_n n:nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | S n' => S n' + sum_1_to_n n'
  end.

(** 1 + 2 + ... + n + (n + 1) = (1 + 2 + ... + n) + (n + 1) *)
Lemma sum_pull_out :
  forall n:nat, sum_1_to_n (S n) = sum_1_to_n n + (S n).
Proof.
  intros.
  simpl.
  induction n.
  auto.
  rewrite <- Nat.add_succ_l.
  rewrite Nat.add_comm.
  reflexivity.
Qed.

Lemma frac_merge :
  forall a b c:nat, b <> 0 -> a / b + c = (a + b * c) / b.
Proof.
  intros.
  rewrite <- Nat.div_add.
  rewrite Nat.mul_comm.
  reflexivity.
  apply H.
Qed.

Lemma add_2_r :
  forall n:nat, n + 2 = S (S n).
Proof.
  intros.
  rewrite <- Nat.add_1_r.
  rewrite Nat.add_succ_r.
  rewrite Nat.add_1_r.
  reflexivity.
Qed.

(** n * (n + 1) / 2 = 1 + 2 + ... + n *)
Theorem sum_eq :
  forall n:nat, sum_1_to_n n = n * (n + 1) / 2.
Proof.
  intros.
  induction n.
  auto.
  rewrite sum_pull_out.
  rewrite IHn.
  rewrite frac_merge.
  repeat rewrite Nat.add_1_r.
  rewrite <- mult_plus_distr_r.
  rewrite Nat.mul_comm.
  rewrite add_2_r.
  reflexivity.
  auto.
Qed.
