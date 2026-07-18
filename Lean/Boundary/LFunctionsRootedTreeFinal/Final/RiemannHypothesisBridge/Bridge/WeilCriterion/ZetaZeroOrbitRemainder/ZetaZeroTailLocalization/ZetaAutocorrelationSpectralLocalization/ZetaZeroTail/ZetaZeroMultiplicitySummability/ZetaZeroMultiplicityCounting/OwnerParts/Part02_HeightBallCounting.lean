import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.OwnerParts.Part01_TsumAndSummandOrder

namespace Boundary
namespace LFunctions

noncomputable section

/-- A completed zero lies in its own centered height ball. -/
theorem zetaCompletedZero_mem_heightBall_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ completedZerosInCenteredHeightBall
      (zetaCompletedZeroCenteredHeight ρ) := by
  exact le_refl (zetaCompletedZeroCenteredHeight ρ)

/-- At its own height, a completed zero contributes its full multiplicity to the
height-ball summand. -/
theorem completedZeroMultiplicityHeightBallSummand_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand
        (zetaCompletedZeroCenteredHeight ρ) ρ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  exact if_pos (le_refl (zetaCompletedZeroCenteredHeight ρ))

/-- Height-ball multiplicity summands vanish outside the height ball. -/
theorem completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredHeightBall T) :
    completedZeroMultiplicityHeightBallSummand T ρ = 0 := by
  exact if_neg hρ

/-- Finite height balls make the height-ball multiplicity summand summable. -/
theorem summable_completedZeroMultiplicityHeightBallSummand_of_finite_heightBall
    (T : ℝ)
    (hfinite : (completedZerosInCenteredHeightBall T).Finite) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand T ρ) := by
  exact summable_of_finite_support_real
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T ρ)
    (completedZerosInCenteredHeightBall T)
    hfinite
    (completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem T)

/-- Height-ball multiplicity summands are summable.

This is the finite-height-ball bookkeeping consequence of local finiteness of the completed
zero divisor, counted with analytic multiplicity. -/
theorem summable_completedZeroMultiplicityHeightBallSummand
    (T : ℝ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand T ρ) := by
  exact summable_completedZeroMultiplicityHeightBallSummand_of_finite_heightBall
    T
    (finite_completedZerosInCenteredHeightBall T)

/-- One nonnegative height-ball summand is bounded by the full height-ball count. -/
theorem completedZeroMultiplicityHeightBallSummand_le_counting
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityCountingInCenteredHeightBall T := by
  exact real_term_le_tsum_of_summable_nonnegative
    (fun η : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T η)
    (summable_completedZeroMultiplicityHeightBallSummand T)
    (completedZeroMultiplicityHeightBallSummand_nonnegative_pointwise T)
    ρ

/-- Completed zero multiplicity counts are nonnegative. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_nonnegative
    (T : ℝ) :
    0 ≤ completedZeroMultiplicityCountingInCenteredHeightBall T := by
  have hzeroSummable :
      Summable
        (fun zeroIndex : {ρ : ℂ // ZetaCompletedZero ρ} =>
          (0 : ℝ)) :=
    summable_zero
  have hsummand :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroMultiplicityHeightBallSummand T ρ) :=
    summable_completedZeroMultiplicityHeightBallSummand T
  have hle :
      (∑' zeroIndex : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ :=
    tsum_le_tsum
      (completedZeroMultiplicityHeightBallSummand_nonnegative_pointwise T)
      hzeroSummable
      hsummand
  have hzero :
      (∑' zeroIndex : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) = 0 :=
    tsum_zero
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ)
    hzero
    hle

/-- Completed zero multiplicity counts are monotone in the height radius. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_mono
    {S T : ℝ} (hST : S ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall S ≤
      completedZeroMultiplicityCountingInCenteredHeightBall T := by
  exact tsum_le_tsum
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand_mono hST ρ)
    (summable_completedZeroMultiplicityHeightBallSummand S)
    (summable_completedZeroMultiplicityHeightBallSummand T)

/-- Each zero's analytic multiplicity is bounded by the height-ball counting function at
that zero's own height. -/
theorem zetaZeroMultiplicity_le_countingFunction_at_height
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall
        (zetaCompletedZeroCenteredHeight ρ) := by
  have hsummand :
      completedZeroMultiplicityHeightBallSummand
          (zetaCompletedZeroCenteredHeight ρ) ρ =
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    completedZeroMultiplicityHeightBallSummand_self ρ
  have hle :
      completedZeroMultiplicityHeightBallSummand
          (zetaCompletedZeroCenteredHeight ρ) ρ ≤
        completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) :=
    completedZeroMultiplicityHeightBallSummand_le_counting
      (zetaCompletedZeroCenteredHeight ρ) ρ
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ completedZeroMultiplicityCountingInCenteredHeightBall
        (zetaCompletedZeroCenteredHeight ρ))
    hsummand
    hle

/-- The complex norm of a natural zero multiplicity is its real cast. -/
theorem norm_complex_ofNat_zetaZeroMultiplicity
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  have hnonneg : 0 ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))
  have hcomplexToReal :
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℝ)‖ :=
    RCLike.norm_ofReal (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  have hrealNorm :
      ‖(zetaZeroMultiplicity (ρ : ℂ) : ℝ)‖ =
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    Real.norm_of_nonneg hnonneg
  exact Eq.trans hcomplexToReal hrealNorm


end

end LFunctions
end Boundary
