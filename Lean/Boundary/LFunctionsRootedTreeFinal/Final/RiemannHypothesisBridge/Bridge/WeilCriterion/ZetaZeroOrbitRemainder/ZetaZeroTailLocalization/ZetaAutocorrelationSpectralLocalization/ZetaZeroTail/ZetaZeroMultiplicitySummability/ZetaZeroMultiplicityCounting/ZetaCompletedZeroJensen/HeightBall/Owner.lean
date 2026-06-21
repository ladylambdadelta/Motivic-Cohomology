import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.JensenBound.Owner

/-!
# Height-ball zero counting

This owner layer transports closed-disk Jensen bounds to centered-height zero counting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Completed zeros in a centered height ball lie in a controlled ordinary closed disk.

The geometric input is the centered critical-strip bound for completed zeros: the real part
is bounded, while the centered height controls the imaginary part. -/
theorem completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ})
    (hρ : zetaCompletedZeroCenteredHeight ρ ≤ T) :
    ‖(ρ : ℂ)‖ ≤ T + 2 := by
  have hstrip :
      -(1 / 2 : ℝ) ≤ (ρ : ℂ).re ∧
        (ρ : ℂ).re ≤ (1 / 2 : ℝ) :=
    zetaCompletedZero_re_mem_centeredCriticalStrip ρ
  have hheight :
      1 + ‖((ρ : ℂ) - (1 / 2 : ℂ)).im‖ ≤ T := by
    exact hρ
  have hbox : (ρ : ℂ) ∈ centeredCriticalHeightBox T :=
    ⟨hstrip.1, hstrip.2, hheight⟩
  have hnorm_radius :
      ‖(ρ : ℂ)‖ ≤ 2 + |T| :=
    centeredCriticalHeightBox_norm_le_radius hbox
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  have habs : |T| = T :=
    abs_of_nonneg hT_nonneg
  have hradius : 2 + |T| = T + 2 := by
    calc
      2 + |T| = 2 + T := by
        exact congrArg (fun x : ℝ => 2 + x) habs
      _ = T + 2 := by
        exact add_comm 2 T
  exact Eq.subst
    (motive := fun x : ℝ => ‖(ρ : ℂ)‖ ≤ x)
    hradius
    hnorm_radius

/-- The height-ball multiplicity summand is pointwise bounded by the corresponding
controlled closed-disk summand. -/
theorem completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand
    (T : ℝ) (hT : 1 ≤ T)
    (ρ : {ρ : ℂ // ZetaCompletedZero ρ}) :
    completedZeroMultiplicityHeightBallSummand T ρ ≤
      completedZeroMultiplicityClosedDiskSummand (T + 2) ρ := by
  exact
    match Decidable.em (zetaCompletedZeroCenteredHeight ρ ≤ T) with
    | Or.inl hheight =>
        have hdisk : ‖(ρ : ℂ)‖ ≤ T + 2 :=
          completedZero_mem_centeredClosedDisk_of_mem_centeredHeightBall
            T hT ρ hheight
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ if ‖(ρ : ℂ)‖ ≤ T + 2 then
              (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
          (if_pos hheight).symm
          (Eq.subst
            (motive := fun x : ℝ =>
              (zetaZeroMultiplicity (ρ : ℂ) : ℝ) ≤ x)
            (if_pos hdisk).symm
            (le_refl (zetaZeroMultiplicity (ρ : ℂ) : ℝ)))
    | Or.inr hheight =>
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ if ‖(ρ : ℂ)‖ ≤ T + 2 then
              (zetaZeroMultiplicity (ρ : ℂ) : ℝ) else 0)
          (if_neg hheight).symm
          (match Decidable.em (‖(ρ : ℂ)‖ ≤ T + 2) with
          | Or.inl hdisk =>
              Eq.subst
                (motive := fun x : ℝ => 0 ≤ x)
                (if_pos hdisk).symm
                (Nat.cast_nonneg (zetaZeroMultiplicity (ρ : ℂ)))
          | Or.inr hdisk =>
              Eq.subst
                (motive := fun x : ℝ => 0 ≤ x)
                (if_neg hdisk).symm
                (le_refl (0 : ℝ)))

/-- Centered-height multiplicity counting is bounded by closed-disk multiplicity counting
at the controlled enlarged radius. -/
theorem completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting
    (T : ℝ) (hT : 1 ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall T ≤
      completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) := by
  exact tsum_le_tsum
    (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
      completedZeroMultiplicityHeightBallSummand_le_closedDiskSummand T hT ρ)
    (summable_completedZeroMultiplicityHeightBallSummand T)
    (summable_completedZeroMultiplicityClosedDiskSummand (T + 2))

/-- A closed-disk polynomial bound at radius `T + 2` gives a centered-height polynomial
bound at radius `T`, after increasing the polynomial constant. -/
theorem completedZeroMultiplicityCounting_heightBall_polynomial_bound_of_closedDisk_bound
    (C : ℝ) (d : ℕ)
    (hC : 0 < C)
    (hclosed :
      ∀ R : ℝ,
        1 ≤ R →
        completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d) :
    ∃ C' : ℝ,
      0 < C' ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C' * T ^ d := by
  exact Exists.intro (C * (3 : ℝ) ^ d)
    (And.intro
      (mul_pos hC (pow_pos zero_lt_three d))
      (fun T hT =>
        have hheight_disk :
            completedZeroMultiplicityCountingInCenteredHeightBall T ≤
              completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) :=
          completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting T hT
        have hR_ge_one : 1 ≤ T + 2 :=
          le_trans hT (le_add_of_nonneg_right zero_le_two)
        have hclosed_T :
            completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) ≤
              C * (T + 2) ^ d :=
          hclosed (T + 2) hR_ge_one
        have htwo_le_two_mul : (2 : ℝ) ≤ 2 * T := by
          calc
            (2 : ℝ) = 2 * 1 := by
              exact (mul_one (2 : ℝ)).symm
            _ ≤ 2 * T := by
              exact mul_le_mul_of_nonneg_left hT zero_le_two
        have hT_add_le_three_mul : T + 2 ≤ (3 : ℝ) * T := by
          have hadd : T + 2 ≤ T + 2 * T :=
            add_le_add_left htwo_le_two_mul T
          have hthree : (3 : ℝ) * T = T + 2 * T := by
            calc
              (3 : ℝ) * T = (2 + 1 : ℝ) * T := by
                exact congrArg (fun x : ℝ => x * T) (two_add_one_eq_three.symm)
              _ = 2 * T + 1 * T := by
                exact add_mul 2 1 T
              _ = 2 * T + T := by
                exact congrArg (fun x : ℝ => 2 * T + x) (one_mul T)
              _ = T + 2 * T := by
                exact add_comm (2 * T) T
          exact Eq.subst
            (motive := fun x : ℝ => T + 2 ≤ x)
            hthree.symm
            hadd
        have hT_add_nonneg : 0 ≤ T + 2 :=
          le_trans zero_le_one hR_ge_one
        have hpow :
            (T + 2) ^ d ≤ ((3 : ℝ) * T) ^ d :=
          pow_le_pow_left₀ hT_add_nonneg hT_add_le_three_mul d
        have hscaled :
            C * (T + 2) ^ d ≤ C * (((3 : ℝ) * T) ^ d) :=
          mul_le_mul_of_nonneg_left hpow (le_of_lt hC)
        have hfactor :
            C * (((3 : ℝ) * T) ^ d) = (C * (3 : ℝ) ^ d) * T ^ d := by
          calc
            C * (((3 : ℝ) * T) ^ d) =
                C * ((3 : ℝ) ^ d * T ^ d) := by
              exact congrArg (fun x : ℝ => C * x) (mul_pow (3 : ℝ) T d)
            _ = (C * (3 : ℝ) ^ d) * T ^ d := by
              exact (mul_assoc C ((3 : ℝ) ^ d) (T ^ d)).symm
        le_trans hheight_disk
          (le_trans hclosed_T
            (le_trans hscaled
              (le_of_eq hfactor)))))

/-- Centered closed-disk zero counting bounds centered-height zero counting after polynomial
radius enlargement. -/
theorem completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (hclosed :
      ∃ C : ℝ, ∃ d : ℕ,
        0 < C ∧
        ∀ R : ℝ,
          1 ≤ R →
          completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    match hclosed with
    | ⟨C, d, hC, hbound⟩ =>
        match completedZeroMultiplicityCounting_heightBall_polynomial_bound_of_closedDisk_bound
            C d hC hbound with
        | ⟨C', hC', hbound'⟩ =>
            ⟨C', d, hC', hbound'⟩

/-- Jensen transport from finite-order growth of the entire zero-carrier to
multiplicity-aware centered-height completed-zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact completedZeroMultiplicityCounting_heightBall_bound_of_closedDisk_bound
    (centeredCompletedRiemannZeta_closedDiskMultiplicityCounting_bound_of_zeroCarrierFiniteOrder
      hfinite)

/-- Jensen transport from finite-order growth of the uncentered entire completed-zeta part
to multiplicity-aware centered-height completed-zero counting. -/
theorem centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_uncenteredFiniteOrder
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_zeroCarrierFiniteOrder
    (centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered huncentered)

/-- Finite-order/Jensen zero counting for the centered completed zeta divisor,
with analytic multiplicities and centered vertical height. -/
theorem centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact
    centeredCompletedRiemannZeta_zeroMultiplicityCounting_height_bound_of_uncenteredFiniteOrder
      (completedRiemannZeta₀_finiteOrder_growth_bound
        hbranch
        hpartialOneTwo htailOneTwo hcompactOneTwo
        hpartialLeft htailBoundary hcompactBoundary)

/-- Coarse polynomial counting of completed zeros with multiplicity in centered
height. -/
theorem exists_completedZeroMultiplicityCounting_height_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (htailOneTwo : PoleClearedOneTwoStripBoundedTailBoundary)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (htailBoundary : PoleClearedRightCriticalStripBoundedTailBoundary)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ C : ℝ, ∃ d : ℕ,
      0 < C ∧
      ∀ T : ℝ,
        1 ≤ T →
        completedZeroMultiplicityCountingInCenteredHeightBall T ≤ C * T ^ d := by
  exact centeredCompletedRiemannZeta_finiteOrder_zeroMultiplicityCounting_height_bound
    hbranch
    hpartialOneTwo htailOneTwo hcompactOneTwo
    hpartialLeft htailBoundary hcompactBoundary


end

end LFunctions
end Boundary
