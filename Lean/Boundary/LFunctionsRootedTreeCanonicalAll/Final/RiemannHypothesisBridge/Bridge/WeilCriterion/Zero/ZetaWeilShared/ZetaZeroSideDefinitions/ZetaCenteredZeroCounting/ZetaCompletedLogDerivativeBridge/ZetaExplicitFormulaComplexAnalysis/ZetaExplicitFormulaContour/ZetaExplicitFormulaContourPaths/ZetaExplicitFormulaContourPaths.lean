import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaContour.ZetaExplicitFormulaRectangleAPI.ZetaExplicitFormulaRectangleAPI
import Mathlib.Analysis.Complex.Basic

/-!
# Boundary explicit-formula contour paths

This file owns the bare path parametrizations for the explicit-formula
rectangle. It is intentionally minimal so both the contour file and the
analytic-control file can consume the same path API without a cycle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The right vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaRightPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => r.c + t * Complex.I

/-- The left vertical side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaLeftPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun t => (1 - r.c) + t * Complex.I

/-- The top horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaTopPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x + r.T * Complex.I

/-- The bottom horizontal side parametrization of the rectangle. -/
def zetaCompletedExplicitFormulaBottomPath
    (r : ExplicitFormulaRectangle) : ℝ → ℂ :=
  fun x => x - r.T * Complex.I

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
