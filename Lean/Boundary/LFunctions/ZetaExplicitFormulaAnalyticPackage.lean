import Boundary.LFunctions.ZetaExplicitFormulaGeometry
import Boundary.LFunctions.ZetaAdmissibleTransformRegularity
import Boundary.LFunctions.ZetaCompletedLogDerivativeControl

/-!
# Boundary explicit-formula analytic package data

This file owns the combined analytic package records used by the completed-zeta
explicit-formula contour argument.  The records are data, not propositions:
they package transform control, completed-log-derivative control, and contour
geometry for downstream theorem wrappers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Owner-level analytic package for a single explicit-formula contour rectangle. -/
structure ExplicitFormulaAnalyticPackage (f : ZetaAdmissibleFunction) where
  phi_control : ZetaPhiAnalyticControl f
  logderiv_control : CompletedZetaNegLogDerivControl f
  contour_data : ExplicitFormulaContourData

/-- Owner-level analytic package for a contour family. -/
structure ExplicitFormulaFamilyAnalyticPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) where
  phi_control : ZetaPhiAnalyticControl f
  logderiv_control : CompletedZetaNegLogDerivControl f

/-- A family package has the same transform-control field as its record projection. -/
theorem ExplicitFormulaFamilyAnalyticPackage.phi_control_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    h.phi_control = h.phi_control :=
  rfl

/-- A family package has the same log-derivative-control field as its record projection. -/
theorem ExplicitFormulaFamilyAnalyticPackage.logderiv_control_eq
    {f : ZetaAdmissibleFunction} {F : ExplicitFormulaContourFamily}
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    h.logderiv_control = h.logderiv_control :=
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
