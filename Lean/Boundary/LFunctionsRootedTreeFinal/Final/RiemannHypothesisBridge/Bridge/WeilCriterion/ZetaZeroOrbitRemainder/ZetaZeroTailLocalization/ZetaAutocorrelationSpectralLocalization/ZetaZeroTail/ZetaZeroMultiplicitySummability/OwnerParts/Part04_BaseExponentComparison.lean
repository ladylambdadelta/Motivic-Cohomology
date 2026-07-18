import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part03_CountingEnvelope

namespace Boundary
namespace LFunctions

noncomputable section

theorem one_add_natNorm_le_two_mul_max_one_natNorm_of_one_le
    (m : ℕ) (hlarge : 1 ≤ ‖((m : ℕ) : ℝ)‖) :
    1 + ‖((m : ℕ) : ℝ)‖ ≤
      (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ := by
  have hmax : max 1 ‖((m : ℕ) : ℝ)‖ = ‖((m : ℕ) : ℝ)‖ :=
    max_eq_right hlarge
  have hadd :
      1 + ‖((m : ℕ) : ℝ)‖ ≤
        ‖((m : ℕ) : ℝ)‖ + ‖((m : ℕ) : ℝ)‖ :=
    add_le_add_right hlarge ‖((m : ℕ) : ℝ)‖
  have hdouble :
      ‖((m : ℕ) : ℝ)‖ + ‖((m : ℕ) : ℝ)‖ =
        (2 : ℝ) * ‖((m : ℕ) : ℝ)‖ :=
    (two_mul ‖((m : ℕ) : ℝ)‖).symm
  have htarget :
      (2 : ℝ) * ‖((m : ℕ) : ℝ)‖ =
        (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ :=
    congrArg (fun value : ℝ => (2 : ℝ) * value) hmax.symm
  exact le_trans hadd (le_of_eq (Eq.trans hdouble htarget))

theorem one_add_natNorm_le_two_mul_max_one_natNorm_of_le_one
    (m : ℕ) (hsmall : ‖((m : ℕ) : ℝ)‖ ≤ 1) :
    1 + ‖((m : ℕ) : ℝ)‖ ≤
      (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ := by
  have hmax : max 1 ‖((m : ℕ) : ℝ)‖ = 1 := max_eq_left hsmall
  have hadd : 1 + ‖((m : ℕ) : ℝ)‖ ≤ 1 + 1 :=
    add_le_add_left hsmall 1
  have hdouble : (1 : ℝ) + 1 = (2 : ℝ) * 1 :=
    (two_mul (1 : ℝ)).symm
  have htarget :
      (2 : ℝ) * 1 = (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ :=
    congrArg (fun value : ℝ => (2 : ℝ) * value) hmax.symm
  exact le_trans hadd (le_of_eq (Eq.trans hdouble htarget))

theorem one_add_natNorm_le_two_mul_max_one_natNorm
    (m : ℕ) :
    1 + ‖((m : ℕ) : ℝ)‖ ≤
      (2 : ℝ) * max 1 ‖((m : ℕ) : ℝ)‖ := by
  exact match (inferInstance : Decidable (1 ≤ ‖((m : ℕ) : ℝ)‖)) with
  | Decidable.isTrue hlarge =>
      one_add_natNorm_le_two_mul_max_one_natNorm_of_one_le m hlarge
  | Decidable.isFalse hlarge =>
      one_add_natNorm_le_two_mul_max_one_natNorm_of_le_one
        m (le_of_not_ge hlarge)

/-- The successor shell endpoint is the canonical tail base. -/
theorem natSucc_cast_eq_one_add_natNorm
    (m : ℕ) :
    (((m + 1 : ℕ) : ℝ)) = 1 + ‖((m : ℕ) : ℝ)‖ := by
  have hm_norm :
      ‖((m : ℕ) : ℝ)‖ = ((m : ℕ) : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg m)
  have hsucc :
      (((m + 1 : ℕ) : ℝ)) = ((m : ℕ) : ℝ) + 1 := by
    have hcast_add :
        (((m + 1 : ℕ) : ℝ)) =
          ((m : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
      Nat.cast_add m 1
    have hcast_one : ((1 : ℕ) : ℝ) = 1 :=
      Nat.cast_one
    exact Eq.trans hcast_add
      (congrArg (fun x : ℝ => ((m : ℕ) : ℝ) + x) hcast_one)
  have hcomm :
      ((m : ℕ) : ℝ) + 1 = 1 + ((m : ℕ) : ℝ) :=
    add_comm ((m : ℕ) : ℝ) 1
  have hnorm :
      1 + ((m : ℕ) : ℝ) = 1 + ‖((m : ℕ) : ℝ)‖ :=
    congrArg (fun x : ℝ => 1 + x) hm_norm.symm
  exact Eq.trans hsucc (Eq.trans hcomm hnorm)

theorem real_growth_decay_numerator_le
    {a b : ℝ} (d D K : ℕ)
    (hb : 1 ≤ b) (hbase : b ≤ (2 : ℝ) * a)
    (hdk : d + K ≤ D) :
    b ^ d * b ^ K ≤ (2 : ℝ) ^ D * a ^ D := by
  have hcombine : b ^ d * b ^ K = b ^ (d + K) :=
    (pow_add b d K).symm
  have hexponent : b ^ (d + K) ≤ b ^ D :=
    pow_le_pow_right₀ hb hdk
  have hbasePower : b ^ D ≤ ((2 : ℝ) * a) ^ D :=
    pow_le_pow_left₀ (le_trans zero_le_one hb) hbase D
  have hproductPower : ((2 : ℝ) * a) ^ D = (2 : ℝ) ^ D * a ^ D :=
    mul_pow (2 : ℝ) a D
  exact le_trans
    (Eq.subst (motive := fun value : ℝ => value ≤ b ^ D)
      hcombine.symm hexponent)
    (le_trans hbasePower (le_of_eq hproductPower))

theorem real_growth_decay_quotient_le
    {a b : ℝ} (d D K : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hbase : b ≤ (2 : ℝ) * a) (hdk : d + K ≤ D) :
    b ^ d / a ^ D ≤ (2 : ℝ) ^ D / b ^ K := by
  have haPowerPositive : 0 < a ^ D :=
    pow_pos (lt_of_lt_of_le zero_lt_one ha) D
  have hbPowerPositive : 0 < b ^ K :=
    pow_pos (lt_of_lt_of_le zero_lt_one hb) K
  exact (div_le_div_iff₀ haPowerPositive hbPowerPositive).mpr
    (real_growth_decay_numerator_le d D K hb hbase hdk)

theorem real_growth_decay_product_eq_quotient
    (a b : ℝ) (d D : ℕ) :
    b ^ d * a ^ (-(D : ℤ)) = b ^ d / a ^ D :=
  Eq.trans
    (congrArg (fun value : ℝ => b ^ d * value)
      (real_zpow_negNat_eq_inv_natPow a D))
    (div_eq_mul_inv (b ^ d) (a ^ D)).symm

theorem real_tail_product_eq_quotient
    (b : ℝ) (D K : ℕ) :
    (2 : ℝ) ^ D * b ^ (-(K : ℤ)) = (2 : ℝ) ^ D / b ^ K :=
  Eq.trans
    (congrArg (fun value : ℝ => (2 : ℝ) ^ D * value)
      (real_zpow_negNat_eq_inv_natPow b K))
    (div_eq_mul_inv ((2 : ℝ) ^ D) (b ^ K)).symm

/-- Abstract exponent bookkeeping for the shell envelope: if `b` is controlled
by `2 * a`, then the growth factor in `b` is absorbed by the stronger decay in
`a`, after enlarging the constant by `2 ^ D`. -/
theorem real_growth_decay_product_le_tail_of_baseComparison
    {a b : ℝ} (d D K : ℕ)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hbase : b ≤ (2 : ℝ) * a)
    (hdk : d + K ≤ D) :
    b ^ d * a ^ (-(D : ℤ)) ≤
      (2 : ℝ) ^ D * b ^ (-(K : ℤ)) := by
  have hdiv :
      b ^ d / a ^ D ≤ (2 : ℝ) ^ D / b ^ K :=
    real_growth_decay_quotient_le d D K ha hb hbase hdk
  have hleft :
      b ^ d * a ^ (-(D : ℤ)) = b ^ d / a ^ D :=
    real_growth_decay_product_eq_quotient a b d D
  have hright :
      (2 : ℝ) ^ D * b ^ (-(K : ℤ)) =
        (2 : ℝ) ^ D / b ^ K :=
    real_tail_product_eq_quotient b D K
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ (2 : ℝ) ^ D * b ^ (-(K : ℤ)))
    hleft.symm
    (Eq.subst
      (motive := fun x : ℝ => b ^ d / a ^ D ≤ x)
      hright.symm
      hdiv)

/-- Multiplying the abstract growth-decay comparison by a positive constant. -/
theorem real_const_mul_growth_decay_product_le_tail_of_baseComparison
    {a b C : ℝ} (d D K : ℕ)
    (hCpos : 0 < C)
    (ha : 1 ≤ a)
    (hb : 1 ≤ b)
    (hbase : b ≤ (2 : ℝ) * a)
    (hdk : d + K ≤ D) :
    C * (b ^ d * a ^ (-(D : ℤ))) ≤
      C * ((2 : ℝ) ^ D * b ^ (-(K : ℤ))) := by
  exact mul_le_mul_of_nonneg_left
    (real_growth_decay_product_le_tail_of_baseComparison
      d D K ha hb hbase hdk)
    (le_of_lt hCpos)

end

end LFunctions
end Boundary
