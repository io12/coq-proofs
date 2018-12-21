(** Proof that the square root of 2 is irrational *)

Require Import Coq.ZArith.Znumtheory.
Require Import Coq.omega.Omega.
Require Import Coq.Reals.Reals.

Open Scope Z_scope.

Lemma even_sqr_even :
  forall n:Z, Zeven (n * n) -> Zeven n.
Proof.
  intros.
  apply Zeven_bool_iff in H.
  apply Zeven_bool_iff.
  rewrite Z.even_mul in H.
  rewrite Bool.orb_diag in H.
  apply H.
Qed.

Lemma even_not_rel_prime :
  forall a b:Z, Zeven a /\ Zeven b -> ~ rel_prime a b.
Proof.
  intros.
  destruct H as [ H_even_a H_even_b ].
  assert (H_b_half_exists : exists b_half : Z, b = 2 * b_half).
  apply Zeven_ex_iff.
  apply H_even_b.
  destruct H_b_half_exists as [ b_half H_b_half_b_eqn ].
  assert (H_a_half_exists : exists a_half : Z, a = 2 * a_half).
  apply Zeven_ex_iff.
  apply H_even_a.
  destruct H_a_half_exists as [ a_half H_a_half_a_eqn ].
  rewrite H_b_half_b_eqn, H_a_half_a_eqn.
  unfold rel_prime.
  intro H_rel_prime.
  remember (Z.gcd a_half b_half) as g.
  assert (H_rel_prime' : Zis_gcd a_half b_half g).
  rewrite Heqg.
  apply Zgcd_is_gcd.
  apply (Zis_gcd_mult _ _ 2 _) in H_rel_prime'.
  apply Zis_gcd_gcd in H_rel_prime.
  apply Zis_gcd_gcd in H_rel_prime'.
  assert (H_1_eq_2_g : 1 = 2 * g).
  congruence.
  assert (H_1_neq_2_g : 1 <> 2 * g).
  omega.
  contradiction.
  assert (H_g_nonneg : 0 <= g).
  rewrite Heqg.
  apply Z.gcd_nonneg.
  omega.
  discriminate.
Qed.

Theorem sqrt_2_irrat :
  (*
    sqrt(2) = b / a
    2 = (b * b) / (a * a)
    b * b = 2 * a * a
  *)
  forall a b:Z, a <> 0 -> b * b = 2 * a * a /\ rel_prime a b -> False.
Proof.
  intros a b H_a_nonzero H.
  destruct H as [ H_b_a_eqn H_rel_prime ].
  assert (H_2_a_sqr_even : Zeven (2 * a * a)).
  rewrite <- Z.mul_assoc.
  apply Zeven_2p.
  assert (H_b_sqr_even : Zeven (b * b)).
  rewrite H_b_a_eqn.
  apply H_2_a_sqr_even.
  clear H_2_a_sqr_even.
  assert (H_b_even : Zeven b).
  apply even_sqr_even.
  apply H_b_sqr_even.
  clear H_b_sqr_even.
  assert (H_c_exists : exists c : Z, b = 2 * c).
  apply Zeven_ex_iff.
  apply H_b_even.
  destruct H_c_exists as [ c H_b_c_eqn ].
  assert (H_c_a_eqn : 2 * c * c = a * a).
  rewrite <- (Z.mul_cancel_l _ _ 2).
  rewrite Z.mul_comm.
  rewrite <- H_b_c_eqn.
  replace (b * c * 2) with (b * (2 * c)) by ring.
  rewrite <- H_b_c_eqn.
  rewrite Z.mul_assoc.
  apply H_b_a_eqn.
  discriminate.
  clear H_b_c_eqn.
  assert (H_2_c_sqr_even : Zeven (2 * c * c)).
  rewrite <- Z.mul_assoc.
  apply Zeven_2p.
  assert (H_a_sqr_even : Zeven (a * a)).
  rewrite <- H_c_a_eqn.
  apply H_2_c_sqr_even.
  clear dependent c.
  assert (H_a_even : Zeven a).
  apply even_sqr_even.
  apply H_a_sqr_even.
  clear H_a_sqr_even.
  assert (H_not_rel_prime : ~ rel_prime a b).
  apply even_not_rel_prime.
  auto.
  contradiction.
Qed.
