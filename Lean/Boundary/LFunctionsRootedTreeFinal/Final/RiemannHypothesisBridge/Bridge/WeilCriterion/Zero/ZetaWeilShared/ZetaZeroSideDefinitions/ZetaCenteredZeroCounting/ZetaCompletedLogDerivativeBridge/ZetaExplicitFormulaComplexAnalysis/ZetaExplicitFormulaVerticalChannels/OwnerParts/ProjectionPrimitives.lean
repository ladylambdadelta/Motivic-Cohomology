import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-! ## Scheduled vertical-channel projection primitives -/

/-- The scheduled horizontal-side contribution of the rectangle. -/
noncomputable def explicitFormulaScheduledHorizontalSideDifference
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaTopLineIntegral f
      (F.rectangle (h.height_schedule.height u)) -
    zetaCompletedExplicitFormulaBottomLineIntegral f
      (F.rectangle (h.height_schedule.height u))

/-- The horizontal-side decay target along the selected schedule.

This is the horizontal estimate in the contour-integral-to-boundary path; it is
recorded as a named step consumed by selected-channel convergence primitives. -/
def explicitFormulaScheduledHorizontalSideDifferenceTendstoZero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F.toContourFamily) : Prop :=
    Tendsto
      (fun u : ℝ =>
        explicitFormulaScheduledHorizontalSideDifference f F.toContourFamily h u)
      atTop
      (𝓝 0)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
