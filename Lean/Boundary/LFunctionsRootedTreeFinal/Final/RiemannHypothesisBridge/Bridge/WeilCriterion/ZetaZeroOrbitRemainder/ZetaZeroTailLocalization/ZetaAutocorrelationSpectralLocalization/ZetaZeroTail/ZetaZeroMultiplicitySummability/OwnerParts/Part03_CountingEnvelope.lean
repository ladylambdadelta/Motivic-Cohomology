import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.OwnerParts.Part02_FiniteCounting

namespace Boundary
namespace LFunctions

noncomputable section

theorem completedZeroCenteredHeightShellDecayMass_le_card_mul_lowerDecay
    (d k m : ℕ) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m := by
  haveI : Fintype (completedZeroCenteredHeightShellFiber m) :=
    (finite_completedZeroCenteredHeightShell m).fintype
  exact real_tsum_le_natCard_mul_of_forall_le
    (fun ρ : completedZeroCenteredHeightShellFiber m =>
      zetaCompletedZeroCenteredHeight
        (ρ.1 : {ρ : ℂ // ZetaCompletedZero ρ}) ^
        (-(d + k + 3 : ℤ)))
    (completedZeroCenteredHeightShellLowerDecay d k m)
    (completedZeroCenteredHeightShell_decay_le_lowerDecay d k m)

/-- Shell decay mass is bounded by the cumulative multiplicity count times the
lower shell decay factor. -/
theorem completedZeroCenteredHeightShellDecayMass_le_counting_mul_lowerDecay
    (d k m : ℕ) :
    completedZeroCenteredHeightShellDecayMass d k m ≤
      completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
        completedZeroCenteredHeightShellLowerDecay d k m := by
  have hcard :
      completedZeroCenteredHeightShellDecayMass d k m ≤
        (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellDecayMass_le_card_mul_lowerDecay d k m
  have hcount :
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) :=
    completedZeroCenteredHeightShell_unweightedCount_le_multiplicityCounting m
  have hdecay_nonnegative :
      0 ≤ completedZeroCenteredHeightShellLowerDecay d k m :=
    completedZeroCenteredHeightShellLowerDecay_nonnegative d k m
  have hmul :
      (Nat.card (completedZeroCenteredHeightShellFiber m) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m ≤
        completedZeroMultiplicityCountingInCenteredHeightBall ((m + 1 : ℕ) : ℝ) *
          completedZeroCenteredHeightShellLowerDecay d k m :=
    mul_le_mul_of_nonneg_right hcount hdecay_nonnegative
  exact le_trans hcard hmul

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
      C d k m hcount)

end

end LFunctions
end Boundary
