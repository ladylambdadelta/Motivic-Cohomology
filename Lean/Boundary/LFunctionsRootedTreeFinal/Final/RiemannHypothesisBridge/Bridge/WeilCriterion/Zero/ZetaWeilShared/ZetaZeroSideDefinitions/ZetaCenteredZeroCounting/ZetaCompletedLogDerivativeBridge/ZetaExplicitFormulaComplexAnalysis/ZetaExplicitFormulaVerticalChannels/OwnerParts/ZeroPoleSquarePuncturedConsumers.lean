import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleFourCellCauchy

/-!
# Direct consumers of the zero-pole square-punctured boundary decomposition

This file contains only wrappers over the concrete equality

`zero-pole square-punctured boundary = zero-pole four-cell boundary sum`.

The equality itself is an oriented-edge bookkeeping theorem; the wrappers here
make the downstream finite Cauchy assembly depend only on that concrete
equality and the already-proved four-cell Cauchy cancellation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- Directly consume a zero-pole square-punctured boundary decomposition
equality to produce square-punctured cancellation from four-cell cancellation. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_squarePuncturedBoundary_eq_zero_of_boundary_eq_fourCell
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ)
    (hboundary :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R)
    (hfour :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R = 0) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      F T R = 0 :=
  Eq.trans hboundary hfour

/-- Canonical-radius version of the direct zero-pole square-punctured
cancellation consumer. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_squarePuncturedBoundary_eq_zero_of_boundary_eq_fourCell_canonicalRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hboundary :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T))
    (hfour :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_squarePuncturedBoundary_eq_zero_of_boundary_eq_fourCell
    f F T (zetaExplicitFormulaZeroPolePunctureRadius F T)
    hboundary hfour

/-- Canonical-radius positive-height square-punctured cancellation for the
isolated `s = 0` correction kernel, assuming the concrete boundary
decomposition equality. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_zero_of_boundary_eq_fourCell
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ}
    (hT : 0 < T)
    (hboundary :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) =
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T)) :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  have hfour :
      zetaExplicitFormulaZeroPoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalFourCellBoundary_eq_zero_of_pos_height
      f F h T hT
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPole_squarePuncturedBoundary_eq_zero_of_boundary_eq_fourCell_canonicalRadius
      f F T hboundary hfour

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
