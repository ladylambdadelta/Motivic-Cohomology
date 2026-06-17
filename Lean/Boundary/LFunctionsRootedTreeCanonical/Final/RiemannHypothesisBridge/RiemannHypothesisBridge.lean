import Boundary.LFunctions.Bridge.WeilCriterion

/-!
# Boundary bridge to mathlib's Riemann hypothesis statement

This file owns the exact namespace alignment between the Boundary
normalization layer and mathlib's public `RiemannHypothesis` constant.
It does not introduce a new analytic criterion; it only exposes the
public theorem surface in a Boundary-owned file so downstream files can
target the official statement directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Boundary's RH statement is exactly mathlib's `RiemannHypothesis`. -/
theorem boundaryRiemannHypothesis_eq_mathlib :
    boundaryRiemannHypothesis = RiemannHypothesis := rfl

/-- Boundary's completed zeta alias is mathlib's completed zeta. -/
theorem boundaryCompletedRiemannZeta_eq_mathlib :
    boundaryCompletedRiemannZeta = completedRiemannZeta := rfl

/-- Boundary's zeta alias is mathlib's Riemann zeta. -/
theorem boundaryRiemannZeta_eq_mathlib :
    boundaryRiemannZeta = riemannZeta := rfl

end
end LFunctions
end Boundary
