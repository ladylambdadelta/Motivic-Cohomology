import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.Owner

/-!
# Single-pole standard rectangle Cauchy assembly

This file owns the algebraic assembly from the punctured-rectangle Cauchy
calculation and the inner residue boundary value to the raw standard rectangle
boundary theorem for the isolated `s = 1` correction kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Algebraic assembly of the raw standard rectangle Cauchy value for the isolated
`s = 1` kernel from the square-punctured rectangle cancellation and the inner
boundary residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero_and_innerSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T R : ℝ}
    (hT_nonneg : 0 ≤ T)
    (hsquare :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R = 0)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hstandard_eq_inner :
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F T =
        zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          R :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardBoundary_eq_innerSquare_of_squarePunctured_zero
      f F hT_nonneg R hsquare
  exact Eq.trans hstandard_eq_inner hinner

/-- Algebraic assembly of the raw standard rectangle Cauchy value from the
four-cell punctured-rectangle cancellation, the boundary decomposition, and the
inner boundary residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_fourCellBoundary_and_innerSquare
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T R : ℝ}
    (hT_nonneg : 0 ≤ T)
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R)
    (hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R = 0)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        R =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hsquare :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T R = 0 :=
    Eq.trans hboundary hfour
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero_and_innerSquare
      f F hT_nonneg hsquare hinner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
