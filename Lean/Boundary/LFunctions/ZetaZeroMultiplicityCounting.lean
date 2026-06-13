import Boundary.LFunctions.ZetaPolynomialTailSummability
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

/-- A nonnegative summable real family dominates each of its terms by its total `tsum`. -/
theorem real_term_le_tsum_of_summable_nonnegative
    {α : Type*} (u : α → ℝ)
    (hu : Summable u)
    (h_nonneg : ∀ a : α, 0 ≤ u a)
    (a : α) :
    u a ≤ ∑' x : α, u x := by
  sorry

/-- Completed zeros in the centered vertical height ball of radius `T`. -/
def completedZerosInCenteredHeightBall (T : ℝ) :
    Set {ρ : ℂ // ZetaCompletedZero ρ} :=
  {ρ | zetaCompletedZeroCenteredHeight ρ ≤ T}

/-- Completed zeros are locally finite in centered height balls.

This is the local-finiteness part of the zero divisor of the completed zeta
function, separated from the later summability bookkeeping. -/
theorem finite_completedZerosInCenteredHeightBall
    (T : ℝ) :
    (completedZerosInCenteredHeightBall T).Finite := by
  sorry

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

/-- Height-ball multiplicity summands are nonnegative. -/
theorem completedZeroMultiplicityHeightBallSummand_nonnegative
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    0 ≤ completedZeroMultiplicityHeightBallSummand T ρ := by
  unfold completedZeroMultiplicityHeightBallSummand
  by_cases hρ : zetaCompletedZeroCenteredHeight ρ ≤ T
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_pos hρ).symm
      (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
  · exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      (if_neg hρ).symm
      (le_refl (0 : ℝ))

/-- Height-ball summands are monotone in the radius. -/
theorem completedZeroMultiplicityHeightBallSummand_mono
    {S T : ℝ} (hST : S ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand S ρ ≤
      completedZeroMultiplicityHeightBallSummand T ρ := by
  unfold completedZeroMultiplicityHeightBallSummand
  by_cases hS : zetaCompletedZeroCenteredHeight ρ ≤ S
  · have hT : zetaCompletedZeroCenteredHeight ρ ≤ T :=
      le_trans hS hST
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
      (if_pos hS).symm
      (Eq.subst
        (motive := fun x : ℝ =>
          (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ x)
        (if_pos hT).symm
        (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))
  · by_cases hT : zetaCompletedZeroCenteredHeight ρ ≤ T
    · exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
        (if_neg hS).symm
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_pos hT).symm
          (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ))))
    · exact Eq.subst
        (motive := fun x : ℝ =>
          x ≤ if zetaCompletedZeroCenteredHeight ρ ≤ T then
            (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
        (if_neg hS).symm
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          (if_neg hT).symm
          (le_refl (0 : ℝ)))

/-- A completed zero lies in its own centered height ball. -/
theorem zetaCompletedZero_mem_heightBall_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    ρ ∈ completedZerosInCenteredHeightBall
      (zetaCompletedZeroCenteredHeight ρ) := by
  unfold completedZerosInCenteredHeightBall
  exact le_refl (zetaCompletedZeroCenteredHeight ρ)

/-- At its own height, a completed zero contributes its full multiplicity to the
height-ball summand. -/
theorem completedZeroMultiplicityHeightBallSummand_self
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand
        (zetaCompletedZeroCenteredHeight ρ) ρ =
      (zetaZeroMultiplicity (ρ : ℂ) : ℝ) := by
  unfold completedZeroMultiplicityHeightBallSummand
  exact if_pos (le_refl (zetaCompletedZeroCenteredHeight ρ))

/-- Height-ball multiplicity summands vanish outside the height ball. -/
theorem completedZeroMultiplicityHeightBallSummand_eq_zero_of_not_mem
    (T : ℝ) (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : ρ ∉ completedZerosInCenteredHeightBall T) :
    completedZeroMultiplicityHeightBallSummand T ρ = 0 := by
  unfold completedZerosInCenteredHeightBall at hρ
  unfold completedZeroMultiplicityHeightBallSummand
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
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  exact real_term_le_tsum_of_summable_nonnegative
    (fun η : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand T η)
    (summable_completedZeroMultiplicityHeightBallSummand T)
    (completedZeroMultiplicityHeightBallSummand_nonnegative T)
    ρ

/-- Completed zero multiplicity counts are nonnegative. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_nonnegative
    (T : ℝ) :
    0 ≤ completedZeroMultiplicityCountingInCenteredHeightBall T := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  have hzeroSummable :
      Summable
        (fun _ρ : {ρ : ℂ // ZetaCompletedZero ρ} => (0 : ℝ)) :=
    summable_zero
  have hsummand :
      Summable
        (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
          completedZeroMultiplicityHeightBallSummand T ρ) :=
    summable_completedZeroMultiplicityHeightBallSummand T
  have hle :
      (∑' _ρ : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ :=
    tsum_le_tsum
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        completedZeroMultiplicityHeightBallSummand_nonnegative T ρ)
      hzeroSummable
      hsummand
  have hzero :
      (∑' _ρ : {ρ : ℂ // ZetaCompletedZero ρ}, (0 : ℝ)) = 0 :=
    tsum_zero
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤
        ∑' ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          completedZeroMultiplicityHeightBallSummand T ρ)
    hzero.symm
    hle

/-- Completed zero multiplicity counts are monotone in the height radius. -/
theorem completedZeroMultiplicityCountingInCenteredHeightBall_mono
    {S T : ℝ} (hST : S ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall S ≤
      completedZeroMultiplicityCountingInCenteredHeightBall T := by
  unfold completedZeroMultiplicityCountingInCenteredHeightBall
  exact tsum_le_tsum
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand_mono hST ρ)
    (summable_completedZeroMultiplicityHeightBallSummand S)
    (summable_completedZeroMultiplicityHeightBallSummand T)

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
theorem summable_completedZero_centeredHeight_negativePower_of_counting_bound
    (C : ℝ) (d k : ℕ)
    (hCpos : 0 < C)
    (hcount :
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  sorry

/-- Polynomial negative-height envelopes are summable over completed zeros. -/
theorem summable_completedZero_centeredHeight_negativePower
    (k : ℕ) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaCompletedZeroCenteredHeight ρ ^ (-(k + 3 : ℤ))) := by
  rcases exists_completedZeroMultiplicityCounting_height_bound with
    ⟨C, d, hCpos, hcount⟩
  exact summable_completedZero_centeredHeight_negativePower_of_counting_bound
    C d k hCpos hcount

end

end LFunctions
end Boundary
