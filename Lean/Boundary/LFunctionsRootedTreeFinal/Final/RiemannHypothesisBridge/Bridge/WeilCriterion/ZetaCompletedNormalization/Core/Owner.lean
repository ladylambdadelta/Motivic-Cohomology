import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Centered completed-zeta core

This file owns the centered completed-zeta objects at the critical line and
their basic analyticity facts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zeta function centered at the critical line. -/
def centeredCompletedRiemannZeta (s : ℂ) : ℂ :=
  completedRiemannZeta (1 / 2 + s)

/-- The entire part of the centered completed zeta function. -/
def centeredCompletedRiemannZeta₀ (s : ℂ) : ℂ :=
  completedRiemannZeta₀ (1 / 2 + s)

/-- The entire zero-carrier for the centered completed zeta function.

Away from the shifted pole faces, zeros of the centered completed zeta
normalization are zeros of this entire carrier.  This is the object to which
Jensen/finite-order zero counting applies; the raw entire part
`centeredCompletedRiemannZeta₀` alone is not the completed-zero divisor. -/
def centeredCompletedRiemannZetaZeroCarrier (s : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + s) *
    (1 - ((1 / 2 : ℂ) + s)) *
      centeredCompletedRiemannZeta₀ s - 1

/-- The quadratic clearing factor used to remove the shifted pole faces from
the centered completed-zeta normalization. -/
def centeredCompletedRiemannZetaZeroCarrierClearingFactor (s : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + s) *
    (1 - ((1 / 2 : ℂ) + s))

/-- The zero-carrier is the centered entire part multiplied by its quadratic
clearing factor, then shifted by `-1`. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_factor_mul_entirePart_sub_one
    (s : ℂ) :
    centeredCompletedRiemannZetaZeroCarrier s =
      centeredCompletedRiemannZetaZeroCarrierClearingFactor s *
        centeredCompletedRiemannZeta₀ s - 1 := by
  rfl

/-- The centered entire part is analytic everywhere. -/
theorem centeredCompletedRiemannZeta₀_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ centeredCompletedRiemannZeta₀ z := by
  have hlinear :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  unfold centeredCompletedRiemannZeta₀
  exact (differentiable_completedZeta₀.analyticAt ((1 / 2 : ℂ) + z)).comp hlinear

/-- The centered zero-carrier is analytic everywhere. -/
theorem centeredCompletedRiemannZetaZeroCarrier_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ centeredCompletedRiemannZetaZeroCarrier z := by
  have hleft :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hright :
      AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
    analyticAt_const.sub (analyticAt_const.add analyticAt_id)
  have hcarrier :
      AnalyticAt ℂ
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + w) *
            (1 - ((1 / 2 : ℂ) + w)) *
              centeredCompletedRiemannZeta₀ w - 1)
        z :=
    ((hleft.mul hright).mul
      (centeredCompletedRiemannZeta₀_analyticAt z)).sub analyticAt_const
  exact hcarrier

end

end LFunctions
end Boundary
