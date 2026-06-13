import Boundary.LFunctions.ZetaZeroSideDefinitions

/-!
# Completed zero multiplicity counting

This file owns the multiplicity-aware zero-counting surface used by the zero-tail
majorant.  The analytic input is the coarse finite-order/Jensen theorem: completed zeta
zeros, counted with analytic multiplicity, have polynomial growth in centered height.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Completed zeros in the centered vertical height ball of radius `T`. -/
def completedZerosInCenteredHeightBall (T : ℝ) :
    Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | zetaCompletedZeroCenteredHeight ρ ≤ T}

/-- The height-ball multiplicity summand. -/
noncomputable def completedZeroMultiplicityHeightBallSummand
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) : ℝ :=
  if zetaCompletedZeroCenteredHeight ρ ≤ T then
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  else
    0

/-- Completed-zero multiplicity count in a centered height ball. -/
noncomputable def completedZeroMultiplicityCountingInCenteredHeightBall
    (T : ℝ) : ℝ :=
  ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
    completedZeroMultiplicityHeightBallSummand T ρ

/-- A completed zero lies in its own centered height ball. -/
theorem zetaCompletedZero_mem_heightBall_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ completedZerosInCenteredHeightBall
      (zetaCompletedZeroCenteredHeight ρ) := by
  unfold completedZerosInCenteredHeightBall
  exact le_refl (zetaCompletedZeroCenteredHeight ρ)

/-- Coarse polynomial counting of completed zeros with multiplicity in centered height.

This is the analytic owner input supplied by Jensen/finite-order theory for the completed
zeta function.  The theorem is deliberately multiplicity-aware so individual
multiplicity growth and zero-tail summability both consume the same source. -/
theorem exists_completedZeroMultiplicityCounting_height_bound :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  sorry

/-- Each zero's analytic multiplicity is bounded by the height-ball counting function at
that zero's own height. -/
theorem zetaZeroMultiplicity_le_countingFunction_at_height
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
      completedZeroMultiplicityCountingInCenteredHeightBall
        (zetaCompletedZeroCenteredHeight ρ) := by
  sorry

/-- The complex norm of a natural zero multiplicity is its real cast. -/
theorem norm_complex_ofNat_zetaZeroMultiplicity
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  have hnonneg : 0 ≤ (zetaZeroMultiplicity (ρ : ℂ) : ℝ) :=
    Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))
  change ‖((zetaZeroMultiplicity (ρ : ℂ) : ℝ) : ℂ)‖ =
    (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
  calc
    ‖((zetaZeroMultiplicity (ρ : ℂ) : ℝ) : ℂ)‖ =
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℝ)‖ := by
      exact Complex.norm_ofReal (zetaZeroMultiplicity (ρ : ℂ) : ℝ)
    _ = (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
      exact Real.norm_of_nonneg hnonneg

/-- Completed-zero multiplicities have polynomial growth in centered height, as a local
consequence of multiplicity-aware zero counting. -/
theorem exists_zetaZeroMultiplicityGrowthEnvelope_bound_from_counting :
    ∃ M : ℝ, ∃ d : ℕ,
      0 < M ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ‖(zetaZeroMultiplicity (ρ : ℂ) : ℂ)‖ ≤
          M * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, d, hCpos, hcount⟩
  refine ⟨C, d, hCpos, ?_⟩
  intro ρ
  have hmult_count :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) :=
    zetaZeroMultiplicity_le_countingFunction_at_height ρ
  have hcount_height :
      completedZeroMultiplicityCountingInCenteredHeightBall
          (zetaCompletedZeroCenteredHeight ρ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    hcount
      (zetaCompletedZeroCenteredHeight ρ)
      (zetaCompletedZeroCenteredHeight_ge_one ρ)
  have hnat_zpow :
      zetaCompletedZeroCenteredHeight ρ ^ d =
        zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) := by
    exact (zpow_natCast (zetaCompletedZeroCenteredHeight ρ) d).symm
  have hbound_nat :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ d :=
    le_trans hmult_count hcount_height
  have hbound_zpow :
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤
        C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ) :=
    Eq.subst
      (motive := fun x : ℝ =>
        (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ C * x)
      hnat_zpow
      hbound_nat
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * zetaCompletedZeroCenteredHeight ρ ^ (d : ℤ))
    (norm_complex_ofNat_zetaZeroMultiplicity ρ).symm
    hbound_zpow

/-- Polynomial negative-height envelopes are summable over completed zeros.

This is the p-series consequence of multiplicity-aware polynomial zero counting. -/
theorem summable_completedZero_centeredHeight_negativePower
    (k : ℕ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  sorry

end

end LFunctions
end Boundary
