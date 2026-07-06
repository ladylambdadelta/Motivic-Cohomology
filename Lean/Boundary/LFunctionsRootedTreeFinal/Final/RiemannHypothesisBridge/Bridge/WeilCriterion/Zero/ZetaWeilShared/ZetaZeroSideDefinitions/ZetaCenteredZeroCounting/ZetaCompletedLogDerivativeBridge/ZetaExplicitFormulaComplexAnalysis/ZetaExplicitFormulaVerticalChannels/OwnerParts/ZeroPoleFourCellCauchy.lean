import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyBottom
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyTop
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyLeft
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchyRight

/-!
# Four-cell Cauchy specialization for the isolated `s = 0` correction pole

This file assembles the four canonical cell cancellations into the finite
four-cell boundary cancellation for the zero-centered punctured rectangle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Canonical four-cell Cauchy cancellation for the isolated `s = 0`
correction kernel at positive height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalFourCellBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  have hbottom :
      zetaExplicitFormulaZeroPoleBottomPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalBottomCellBoundary_eq_zero_of_pos_height
      f F h T hT
  have htop :
      zetaExplicitFormulaZeroPoleTopPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalTopCellBoundary_eq_zero_of_pos_height
      f F h T hT
  have hleft :
      zetaExplicitFormulaZeroPoleLeftPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalLeftCellBoundary_eq_zero_of_pos_height
      f F h T hT
  have hright :
      zetaExplicitFormulaZeroPoleRightPunctureCellBoundaryIntegral
        (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
        F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalRightCellBoundary_eq_zero_of_pos_height
      f F h T hT
  exact
    zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum_eq_zero_of_cells
      (zetaCompletedExplicitFormulaCorrectionZeroPoleKernelFn f)
      F T R hbottom htop hleft hright

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
