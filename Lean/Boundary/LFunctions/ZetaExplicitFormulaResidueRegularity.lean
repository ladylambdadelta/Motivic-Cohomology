import Boundary.LFunctions.ZetaExplicitFormulaContour
import Boundary.LFunctions.ZetaExplicitFormulaAnalyticPackage

/-!
# Boundary explicit-formula residue regularity

This file owns the analytic regularity input for the residue stage of the
completed-zeta contour argument.  The singular set includes the poles at `0`
and `1` and the zeros of the completed zeta factor; away from that set the
full contour integrand, including `completedZetaNegLogDeriv`, is differentiable.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The full completed-zeta contour-integrand singular set used in the residue argument. -/
def completedZetaContourIntegrandSingularSet : Set ℂ :=
  {z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)}

/-- The named singular-set definition unfolds to the completed-zeta singular-set predicate. -/
theorem completedZetaContourIntegrandSingularSet_eq :
    completedZetaContourIntegrandSingularSet =
      ({z : ℂ | z = 0 ∨ z = 1 ∨
        (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} : Set ℂ) :=
  rfl

/-- The full completed-zeta contour-integrand singular set is countable. -/
theorem completedZetaContourIntegrandSingularSet_countable :
    completedZetaContourIntegrandSingularSet.Countable :=
  contourIntegrand_singularSet_countable

/-- Outside the full completed-zeta contour-integrand singular set, the integrand is
complex differentiable. -/
theorem completedZetaContourIntegrand_differentiableAt_off_singularSet
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  contourIntegrand_differentiableAt_off_countable hPhi hz

/-- Outside the full completed-zeta contour-integrand singular set, the integrand is
continuous. -/
theorem completedZetaContourIntegrand_continuousAt_off_singularSet
    {f : ZetaAdmissibleFunction} (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  (completedZetaContourIntegrand_differentiableAt_off_singularSet hPhi hz).continuousAt

/-- The package-level residue regularity theorem for the full completed-zeta contour integrand. -/
theorem completedZetaContourIntegrand_regularAt_off_singularSet
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ} (hz : z ∉ completedZetaContourIntegrandSingularSet) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  And.intro
    (completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hz)
    (completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hz)

/-- The residue-argument singular set for the rectangle formula is countable. -/
theorem completedZeta_rectangleResidueFormula_singularSet_countable
    {f : ZetaAdmissibleFunction} (_h : ExplicitFormulaAnalyticPackage f) :
    ({z : ℂ | z = 0 ∨ z = 1 ∨ (z ≠ 0 ∧ z ≠ 1 ∧ completedRiemannZeta z = 0)} :
      Set ℂ).Countable :=
  completedZetaContourIntegrandSingularSet_countable

/-- Away from the completed-zeta singular set, the full contour integrand is continuous. -/
theorem completedZeta_rectangleResidueFormula_continuousOn
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_continuousAt_off_singularSet h.phi_control hz

/-- Away from the completed-zeta singular set, the full contour integrand is differentiable. -/
theorem completedZeta_rectangleResidueFormula_differentiableAt
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  completedZetaContourIntegrand_differentiableAt_off_singularSet h.phi_control hz

/-- The package exposes the owner-level countable-singular-set regularity theorem. -/
theorem completedZeta_rectangleResidueFormula_regular_off_countable
    {f : ZetaAdmissibleFunction} (h : ExplicitFormulaAnalyticPackage f)
    {z : ℂ}
    (hz : z ∉ ({w : ℂ | w = 0 ∨ w = 1 ∨
      (w ≠ 0 ∧ w ≠ 1 ∧ completedRiemannZeta w = 0)} : Set ℂ)) :
    ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
      DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
  And.intro
    (completedZeta_rectangleResidueFormula_continuousOn h hz)
    (completedZeta_rectangleResidueFormula_differentiableAt h hz)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
