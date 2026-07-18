import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.HeightBall.OwnerParts.Part03_HeightCounting

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Multiplication by two preserves the lower bound one. -/
theorem two_le_two_mul_of_one_le
    (T : ℝ) (hT : 1 ≤ T) :
    (2 : ℝ) ≤ 2 * T := by
  have htwo : (2 : ℝ) = 2 * 1 :=
    (mul_one (2 : ℝ)).symm
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 2 * T)
    htwo.symm
    (mul_le_mul_of_nonneg_left hT zero_le_two)

/-- Radius enlargement by two is bounded by multiplication by three. -/
theorem add_two_le_three_mul_of_one_le
    (T : ℝ) (hT : 1 ≤ T) :
    T + 2 ≤ (3 : ℝ) * T := by
  have hadd : T + 2 ≤ T + 2 * T :=
    add_le_add_left (two_le_two_mul_of_one_le T hT) T
  have hthreeOne : (3 : ℝ) * T = (2 + 1 : ℝ) * T :=
    congrArg (fun x : ℝ => x * T) (two_add_one_eq_three.symm)
  have hthreeTwo : (2 + 1 : ℝ) * T = 2 * T + 1 * T :=
    add_mul 2 1 T
  have hthreeThree : 2 * T + 1 * T = 2 * T + T :=
    congrArg (fun x : ℝ => 2 * T + x) (one_mul T)
  have hthreeFour : 2 * T + T = T + 2 * T :=
    add_comm (2 * T) T
  have hthree : (3 : ℝ) * T = T + 2 * T :=
    Eq.trans hthreeOne (Eq.trans hthreeTwo (Eq.trans hthreeThree hthreeFour))
  exact Eq.subst
    (motive := fun x : ℝ => T + 2 ≤ x)
    hthree.symm
    hadd

/-- The enlarged radius power is bounded by the scaled radius power. -/
theorem add_two_pow_le_three_mul_pow
    (T : ℝ) (d : ℕ) (hT : 1 ≤ T) :
    (T + 2) ^ d ≤ ((3 : ℝ) * T) ^ d := by
  have hR : 1 ≤ T + 2 :=
    le_trans hT (le_add_of_nonneg_right zero_le_two)
  have hnonnegative : 0 ≤ T + 2 :=
    le_trans zero_le_one hR
  exact pow_le_pow_left₀ hnonnegative
    (add_two_le_three_mul_of_one_le T hT) d

/-- The scaled radius power factors into the chosen constant and the height power. -/
theorem scaled_three_mul_pow_factor
    (C T : ℝ) (d : ℕ) :
    C * (((3 : ℝ) * T) ^ d) =
      (C * (3 : ℝ) ^ d) * T ^ d := by
  have hpow :
      C * (((3 : ℝ) * T) ^ d) =
        C * ((3 : ℝ) ^ d * T ^ d) :=
    congrArg (fun x : ℝ => C * x) (mul_pow (3 : ℝ) T d)
  exact Eq.trans hpow (mul_assoc C ((3 : ℝ) ^ d) (T ^ d)).symm

/-- The closed-disk polynomial bound transports pointwise to the height ball. -/
theorem completedZeroMultiplicityCounting_heightBall_pointwise_polynomial_bound
    (C : ℝ) (d : ℕ)
    (hC : 0 < C)
    (hclosed :
      ∀ R : ℝ,
        1 ≤ R →
        completedZeroMultiplicityCountingInCenteredClosedDisk R ≤ C * R ^ d)
    (T : ℝ) (hT : 1 ≤ T) :
    completedZeroMultiplicityCountingInCenteredHeightBall T ≤
      (C * (3 : ℝ) ^ d) * T ^ d := by
  have hheight :
      completedZeroMultiplicityCountingInCenteredHeightBall T ≤
        completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) :=
    completedZeroMultiplicityCounting_heightBall_le_closedDiskCounting T hT
  have hR : 1 ≤ T + 2 :=
    le_trans hT (le_add_of_nonneg_right zero_le_two)
  have hclosedT :
      completedZeroMultiplicityCountingInCenteredClosedDisk (T + 2) ≤
        C * (T + 2) ^ d :=
    hclosed (T + 2) hR
  have hscaled :
      C * (T + 2) ^ d ≤ C * (((3 : ℝ) * T) ^ d) :=
    mul_le_mul_of_nonneg_left
      (add_two_pow_le_three_mul_pow T d hT)
      (le_of_lt hC)
  have hfactor :
      C * (((3 : ℝ) * T) ^ d) =
        (C * (3 : ℝ) ^ d) * T ^ d :=
    scaled_three_mul_pow_factor C T d
  exact le_trans hheight
    (le_trans hclosedT
      (le_trans hscaled (le_of_eq hfactor)))

/-- A disk polynomial bound gives a height-ball polynomial bound after radius enlargement. -/
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
      (completedZeroMultiplicityCounting_heightBall_pointwise_polynomial_bound
        C d hC hclosed))
end

end LFunctions
end Boundary
