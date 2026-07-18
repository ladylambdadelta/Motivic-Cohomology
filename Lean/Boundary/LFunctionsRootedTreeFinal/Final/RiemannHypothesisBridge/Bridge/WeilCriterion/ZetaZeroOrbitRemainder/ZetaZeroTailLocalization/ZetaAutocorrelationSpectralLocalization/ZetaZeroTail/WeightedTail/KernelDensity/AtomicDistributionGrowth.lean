import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.WeightedTail.KernelDensity.AtomicDistributionFiberTomography
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.GrowthDecayBounds.Owner

/-!
# Polynomial growth of completed-zero atomic coefficients

The atomic uniqueness theorem is stated for the natural distributional class:
coefficients of polynomial growth in centered completed-zero height.  Jensen
counting and Paley-Wiener rapid decay make this class continuous on the
admissible compactly supported smooth probe space.
-/

namespace Boundary
namespace LFunctions
noncomputable section
namespace ZetaAdmissibleFunction

/-- Polynomial growth in the canonical centered completed-zero height. -/
def CompletedZeroAtomicPolynomialGrowth
    (coefficient : ZetaCompletedZeroCoordinate → ℂ) : Prop :=
  ∃ bound : ℝ,
    ∃ degree : ℕ,
      0 ≤ bound ∧
        ∀ rho : ZetaCompletedZeroCoordinate,
          ‖coefficient rho‖ ≤
            bound * zetaCompletedZeroCenteredHeight rho ^ degree

/-- The zero coefficient family has polynomial growth. -/
theorem completedZeroAtomicPolynomialGrowth_zero :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho : ZetaCompletedZeroCoordinate => (0 : ℂ)) :=
  Exists.intro 0
    (Exists.intro 0
      (And.intro
        (le_refl 0)
        (fun rho =>
          Eq.subst
            (motive := fun value : ℝ => value ≤ 0 *
              zetaCompletedZeroCenteredHeight rho ^ 0)
            (norm_zero : ‖(0 : ℂ)‖ = 0).symm
            (Eq.subst
              (motive := fun value : ℝ => 0 ≤ value)
              (zero_mul (zetaCompletedZeroCenteredHeight rho ^ 0)).symm
              (le_refl 0)))))

/-- A pointwise norm bound transports polynomial growth to a second family. -/
theorem CompletedZeroAtomicPolynomialGrowth.of_norm_le
    (left right : ZetaCompletedZeroCoordinate → ℂ)
    (hright : CompletedZeroAtomicPolynomialGrowth right)
    (hbound : ∀ rho : ZetaCompletedZeroCoordinate,
      ‖left rho‖ ≤ ‖right rho‖) :
    CompletedZeroAtomicPolynomialGrowth left :=
  match hright with
  | ⟨bound, degree, hboundNonnegative, hrightBound⟩ =>
      ⟨bound, degree, hboundNonnegative,
        fun rho => le_trans (hbound rho) (hrightBound rho)⟩

/-- Multiplication by a uniformly bounded coefficient preserves polynomial
growth. -/
theorem CompletedZeroAtomicPolynomialGrowth.mul_bounded_left
    (coefficient : ZetaCompletedZeroCoordinate → ℂ)
    (boundedCoefficient : ZetaCompletedZeroCoordinate → ℂ)
    (hgrowth : CompletedZeroAtomicPolynomialGrowth coefficient)
    (bound : ℝ)
    (hboundNonnegative : 0 ≤ bound)
    (hbounded : ∀ rho : ZetaCompletedZeroCoordinate,
      ‖boundedCoefficient rho‖ ≤ bound) :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho => boundedCoefficient rho * coefficient rho) :=
  match hgrowth with
  | ⟨growthBound, degree, hgrowthBoundNonnegative, hcoefficientBound⟩ =>
      ⟨bound * growthBound, degree,
        mul_nonneg hboundNonnegative hgrowthBoundNonnegative,
        fun rho =>
          have hcoefficientNormNonnegative : 0 ≤ ‖coefficient rho‖ :=
            norm_nonneg (coefficient rho)
          have hgrowthEnvelopeNonnegative :
              0 ≤ growthBound * zetaCompletedZeroCenteredHeight rho ^ degree :=
            le_trans hcoefficientNormNonnegative (hcoefficientBound rho)
          calc
            ‖boundedCoefficient rho * coefficient rho‖ =
                ‖boundedCoefficient rho‖ * ‖coefficient rho‖ :=
              norm_mul (boundedCoefficient rho) (coefficient rho)
            _ ≤ bound *
                (growthBound * zetaCompletedZeroCenteredHeight rho ^ degree) :=
              mul_le_mul
                (hbounded rho)
                (hcoefficientBound rho)
                hcoefficientNormNonnegative
                hboundNonnegative
            _ = (bound * growthBound) *
                zetaCompletedZeroCenteredHeight rho ^ degree :=
              (mul_assoc bound growthBound
                (zetaCompletedZeroCenteredHeight rho ^ degree)).symm⟩

/-- Products of polynomial-growth completed-zero coefficient families have
polynomial growth, with degrees added. -/
theorem CompletedZeroAtomicPolynomialGrowth.mul
    (left right : ZetaCompletedZeroCoordinate → ℂ)
    (hleft : CompletedZeroAtomicPolynomialGrowth left)
    (hright : CompletedZeroAtomicPolynomialGrowth right) :
    CompletedZeroAtomicPolynomialGrowth
      (fun rho => left rho * right rho) :=
  match hleft, hright with
  | ⟨leftBound, leftDegree, hleftBoundNonnegative, hleftEstimate⟩,
      ⟨rightBound, rightDegree, hrightBoundNonnegative, hrightEstimate⟩ =>
      ⟨leftBound * rightBound, leftDegree + rightDegree,
        mul_nonneg hleftBoundNonnegative hrightBoundNonnegative,
        fun rho =>
          have hleftNormNonnegative : 0 ≤ ‖left rho‖ :=
            norm_nonneg (left rho)
          have hrightEnvelopeNonnegative :
              0 ≤ rightBound *
                zetaCompletedZeroCenteredHeight rho ^ rightDegree :=
            le_trans (norm_nonneg (right rho)) (hrightEstimate rho)
          calc
            ‖left rho * right rho‖ = ‖left rho‖ * ‖right rho‖ :=
              norm_mul (left rho) (right rho)
            _ ≤
                (leftBound * zetaCompletedZeroCenteredHeight rho ^ leftDegree) *
                  (rightBound * zetaCompletedZeroCenteredHeight rho ^ rightDegree) :=
              mul_le_mul
                (hleftEstimate rho)
                (hrightEstimate rho)
                (norm_nonneg (right rho))
                (le_trans hleftNormNonnegative (hleftEstimate rho))
            _ = (leftBound * rightBound) *
                zetaCompletedZeroCenteredHeight rho ^
                  (leftDegree + rightDegree) := by
              calc
                (leftBound * zetaCompletedZeroCenteredHeight rho ^ leftDegree) *
                    (rightBound * zetaCompletedZeroCenteredHeight rho ^ rightDegree) =
                    (leftBound * rightBound) *
                      (zetaCompletedZeroCenteredHeight rho ^ leftDegree *
                        zetaCompletedZeroCenteredHeight rho ^ rightDegree) :=
                  mul_mul_mul_comm leftBound
                    (zetaCompletedZeroCenteredHeight rho ^ leftDegree)
                    rightBound
                    (zetaCompletedZeroCenteredHeight rho ^ rightDegree)
                _ = (leftBound * rightBound) *
                    zetaCompletedZeroCenteredHeight rho ^
                      (leftDegree + rightDegree) :=
                  congrArg
                    (fun value : ℝ => (leftBound * rightBound) * value)
                    (pow_add
                      (zetaCompletedZeroCenteredHeight rho)
                      leftDegree rightDegree).symm⟩

end ZetaAdmissibleFunction
end
end LFunctions
end Boundary
