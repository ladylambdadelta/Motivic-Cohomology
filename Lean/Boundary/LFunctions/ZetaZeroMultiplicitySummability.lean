import Boundary.LFunctions.ZetaZeroMultiplicityCounting

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

/-- The lower decay factor attached to a centered-height shell. -/
noncomputable def completedZeroCenteredHeightShellLowerDecay
    (d k m : ℕ) : ℝ :=
  (max 1 ‖((m : ℕ) : ℝ)‖) ^ (-(d + k + 3 : ℤ))

/-- The lower shell decay factor is nonnegative. -/
theorem completedZeroCenteredHeightShellLowerDecay_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellLowerDecay d k m := by
  unfold completedZeroCenteredHeightShellLowerDecay
  exact zpow_nonneg
    (le_trans zero_le_one (le_max_left 1 ‖((m : ℕ) : ℝ)‖))
    (-(d + k + 3 : ℤ))

/-- A centered-height shell decay mass is nonnegative. -/
theorem completedZeroCenteredHeightShellDecayMass_nonnegative
    (d k m : ℕ) :
    0 ≤ completedZeroCenteredHeightShellDecayMass d k m := by
  unfold completedZeroCenteredHeightShellDecayMass
  exact tsum_nonneg
    (fun x : completedZeroCenteredHeightShellFiber m =>
      zpow_nonneg
        (le_trans zero_le_one
          (zetaCompletedZeroCenteredHeight_ge_one
            (x : {ρ : ℂ // ZetaCompletedZero ρ})))
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
  exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le m))

/-- Shell decay mass is bounded by the cumulative multiplicity count times the
lower shell decay factor. -/
theorem completedZeroCenteredHeightShellDecayMass_le_counting_mul_lowerDecay
    (d k m : ℕ) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m := by
  sorry

/-- Applying a counting bound converts the counting-times-decay expression into
the named cumulative shell envelope. -/
theorem completedZeroMultiplicityCounting_mul_lowerDecay_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hcount_m :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) ≤
        C * (((m + 1 : ℕ) : ℝ) ^ d)) :
    completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  have hdecay_nonnegative :
      0 ≤ completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellLowerDecay_nonnegative d k m
  have hmul :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m ≤
        (C * (((m + 1 : ℕ) : ℝ) ^ d)) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    mul_le_mul_of_nonneg_right hcount_m hdecay_nonnegative
  exact hmul

/-- Multiplicity-aware counting bounds the real shell decay mass by the raw
cumulative shell envelope. -/
theorem completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  have hshell :
      completedZeroCenteredHeightShellDecayMass d k m ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellDecayMass_le_counting_mul_lowerDecay d k m
  have hcount_m :
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) ≤
        C * (((m + 1 : ℕ) : ℝ) ^ d) :=
    hcount
      ((m + 1 : ℕ) : ℝ)
      (one_le_nat_succ_cast_real m)
  exact le_trans hshell
    (completedZeroMultiplicityCounting_mul_lowerDecay_le_countingEnvelope
      C d k m hcount_m)

/-- Multiplicity-aware counting dominates the unweighted shell decay by the
raw cumulative shell envelope. -/
theorem norm_completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
    (C : ℝ) (d k m : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ‖completedZeroCenteredHeightShellDecayMass d k m‖ ≤
      completedZeroCenteredHeightShellCountingEnvelope C d k m := by
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroCenteredHeightShellCountingEnvelope C d k m)
    (norm_completedZeroCenteredHeightShellDecayMass_eq_self d k m).symm
    (completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
      C d k m hCpos hcount)

/-- The cumulative shell envelope is bounded by a one-dimensional polynomial
tail after increasing the constant. -/
theorem exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        completedZeroCenteredHeightShellCountingEnvelope C d k m ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  sorry

/-- Multiplicity-aware counting dominates the unweighted shell decay by a
one-dimensional polynomial tail after increasing the constant.

This is the exact estimate where positive zero multiplicity, shell containment,
and exponent bookkeeping meet. -/
theorem exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ m : ℕ,
        ‖completedZeroCenteredHeightShellDecayMass d k m‖ ≤
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  rcases exists_completedZeroCenteredHeightShellCountingEnvelope_le_polynomialTail
      C d k hCpos with
    ⟨A, hApos, hA⟩
  exact ⟨A, hApos, fun m =>
    le_trans
      (norm_completedZeroCenteredHeightShellDecayMass_le_countingEnvelope
        C d k m hCpos hcount)
      (hA m)⟩

/-- The degree-aware shell masses are summable under the polynomial
multiplicity-counting bound. -/
theorem summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun m : ℕ =>
        completedZeroCenteredHeightShellDecayMass d k m) := by
  rcases exists_norm_completedZeroCenteredHeightShellDecayMass_le_polynomialTail_of_counting_bound
      C d k hCpos hcount with
    ⟨A, _hApos, hA⟩
  have htail :
      Summable
        (fun m : ℕ =>
          A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) :=
    (summable_one_add_nat_norm_negative_zpow_succ k).const_mul A
  exact Summable.of_norm_bounded
    (fun m : ℕ =>
      A * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
    htail
    hA

/-- Polynomial negative-height envelopes are summable over completed zeros once
the decay exponent is chosen beyond the counting degree.

This is the p-series consequence of multiplicity-aware polynomial zero counting. -/
theorem summable_completedZero_centeredHeight_negativePower_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  exact summable_completedZero_centeredHeight_negativePower_of_shellMass
    d
    k
    (summable_completedZeroCenteredHeightShellDecayMass_of_counting_bound
      C d k hCpos hcount)

/-- The completed-zero counting theorem supplies a counting degree after which
all further polynomial negative-height envelopes are summable. -/
theorem exists_summable_completedZero_centeredHeight_negativePower_with_countingMargin :
    ∃ d : ℕ,
      ∀ k : ℕ,
        Summable
          (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
            zetaCompletedZeroCenteredHeight ρ ^ (-(d + k + 3 : ℤ))) := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, d, hCpos, hcount⟩
  refine ⟨d, ?_⟩
  intro k
  exact summable_completedZero_centeredHeight_negativePower_of_counting_bound
    C d k hCpos hcount

end

end LFunctions
end Boundary
