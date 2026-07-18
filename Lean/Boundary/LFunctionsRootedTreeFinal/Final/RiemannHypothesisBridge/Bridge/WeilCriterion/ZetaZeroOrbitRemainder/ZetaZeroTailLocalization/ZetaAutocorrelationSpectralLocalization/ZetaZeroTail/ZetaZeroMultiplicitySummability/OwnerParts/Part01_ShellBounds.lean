import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.Owner

/-!
# Completed zero multiplicity summability

This file owns the passage from multiplicity-aware height counting to summability
of negative centered-height powers over completed zeros.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The cumulative counting envelope controlling one centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellCountingEnvelope
    (C : ℝ) (d k m : ℕ) : ℝ :=
  C * (((m + 1 : ℕ) : ℝ) ^ d) *
    (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))

/-- The explicit constant used to dominate the shell counting envelope by a
one-dimensional polynomial tail. -/
noncomputable def completedZeroCenteredHeightShellTailConstant
    (C : ℝ) (d k : ℕ) : ℝ :=
  C * (2 : ℝ) ^ (d + k + 3)

/-- The explicit shell-tail constant is positive when `C` is positive. -/
theorem completedZeroCenteredHeightShellTailConstant_pos
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C) :
    0 < completedZeroCenteredHeightShellTailConstant C d k := by
  exact mul_pos hCpos (pow_pos zero_lt_two (d + k + 3))

/-- The lower decay factor attached to a centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellLowerDecay
    (d k m : ℕ) : ℝ :=
  (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))

/-- The lower shell decay factor is nonnegative. -/
theorem completedZeroCenteredHeightShellLowerDecay_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellLowerDecay d k m := by
  exact zpow_nonneg
    (le_trans zero_le_one (le_max_left 1 ‖((m : ℕ) : ℝ)‖))
    (-(d + k + 3 : ℤ))

/-- A centered-height shell decay mass is nonnegative. -/
theorem completedZeroCenteredHeightShellDecayMass_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellDecayMass d k m := by
  exact tsum_nonneg
    (fun x : completedZeroCenteredHeightShellFiber m =>
      zpow_nonneg
        (le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one
            (x.1 : {ρ : ℂ // ZetaCompletedZero ρ})))
        (-(d + k + 3 : ℤ)))

/-- The norm of a centered-height shell decay mass is the mass itself. -/
theorem norm_completedZeroCenteredHeightShellDecayMass_eq_self
    (d k m : ℕ) :
    ‖completedZeroCenteredHeightShellDecayMass d k m‖ =
      completedZeroCenteredHeightShellDecayMass d k m := by
  exact Real.norm_of_nonneg
    (completedZeroCenteredHeightShellDecayMass_nonnegative d k m)

/-- A successor natural, cast to `ℝ`, is at least one. -/
theorem one_le_nat_succ_cast_real
    (m : ℕ) :
    1 ≤ ((m + 1 : ℕ) : ℝ) := by
  have hcast :
      ((1 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le m))
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ ((m + 1 : ℕ) : ℝ))
    Nat.cast_one
    hcast

theorem real_zpow_negNat_eq_inv_natPow
    (a : ℝ) (N : ℕ) :
    a ^ (-(N : ℤ)) = (a ^ N)⁻¹ := by
  have hnegative : a ^ (-(N : ℤ)) = (a ^ (N : ℤ))⁻¹ :=
    zpow_neg a (N : ℤ)
  have hnatural : a ^ (N : ℤ) = a ^ N := zpow_natCast a N
  exact Eq.trans hnegative (congrArg Inv.inv hnatural)

/-- On bases at least one, negative natural integer powers are antitone. -/
theorem real_zpow_negNat_antitone_on_one_le
    {a b : ℝ} (N : ℕ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    b ^ (-(N : ℤ)) ≤ a ^ (-(N : ℤ)) := by
  have ha_pos : 0 < a :=
    lt_of_lt_of_le zero_lt_one ha
  have hpow_le :
      a ^ N ≤ b ^ N :=
    pow_le_pow_left₀ (le_of_lt ha_pos) hab N
  have ha_pow_pos :
      0 < a ^ N :=
    pow_pos ha_pos N
  have hinv :
      (b ^ N)⁻¹ ≤ (a ^ N)⁻¹ :=
    inv_anti₀ ha_pow_pos hpow_le
  have hb_zpow := real_zpow_negNat_eq_inv_natPow b N
  have ha_zpow := real_zpow_negNat_eq_inv_natPow a N
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ a ^ (-(N : ℤ)))
    hb_zpow.symm
    (Eq.subst
      (motive := fun x : ℝ => (b ^ N)⁻¹ ≤ x)
      ha_zpow.symm
      hinv)

/-- The lower shell base is below the centered height of each zero in the shell. -/
theorem completedZeroCenteredHeightShell_lowerBase_le_height
    (m : ℕ)
    (ρ : completedZeroCenteredHeightShellFiber m) :
    max 1 ‖((m : ℕ) : ℝ)‖ ≤
      zetaCompletedZeroCenteredHeight
        (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) := by
  have hheight_ge_one :
      1 ≤ zetaCompletedZeroCenteredHeight
        (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    zetaCompletedZeroCenteredHeight_ge_one
      (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ})
  have hm_cast_le_height :
      ((m : ℕ) : ℝ) ≤
        zetaCompletedZeroCenteredHeight
          (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    ρ.2.1
  have hm_norm_eq :
      ‖((m : ℕ) : ℝ)‖ = ((m : ℕ) : ℝ) :=
    Real.norm_of_nonneg (Nat.cast_nonneg m)
  have hm_norm_le_height :
      ‖((m : ℕ) : ℝ)‖ ≤
        zetaCompletedZeroCenteredHeight
          (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) :=
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ zetaCompletedZeroCenteredHeight
          (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}))
      hm_norm_eq.symm
      hm_cast_le_height
  exact max_le hheight_ge_one hm_norm_le_height

/-- A completed zero in shell `m` has its decay term bounded by the lower shell
decay factor. -/
theorem completedZeroCenteredHeightShell_decay_le_lowerDecay
    (d k m : ℕ)
    (ρ : completedZeroCenteredHeightShellFiber m) :
    zetaCompletedZeroCenteredHeight
        (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ)) ≤
      completedZeroCenteredHeightShellLowerDecay d k m := by
  exact real_zpow_negNat_antitone_on_one_le
    (d + k + 3)
    (le_max_left 1 ‖((m : ℕ) : ℝ)‖)
    (completedZeroCenteredHeightShell_lowerBase_le_height m ρ)

end

end LFunctions
end Boundary
