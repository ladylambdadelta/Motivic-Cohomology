import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.OnePoleFourCellCauchy
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.SquarePuncturedEdgeIntegrals

/-!
# Positive-height raw Cauchy theorem for the isolated `s = 1` correction pole

This file owns the final finite single-pole contour assembly at positive height.
It sits below the square-punctured boundary split, the four-cell Cauchy
cancellation, and the inner-square residue calculation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Algebraic assembly of the positive-height raw standard Cauchy value for
the isolated `s = 1` correction kernel from the two finite contour inputs:
the square-punctured rectangle boundary vanishes and the inner puncture square
has the deleted-pole residue value.

The analytic work is intentionally not hidden here; this theorem only consumes
the two contour facts at the canonical one-pole puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_canonicalPunctureInputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T)
    (hsquare :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0)
    (hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  exact
    Eq.trans
      (zetaCompletedExplicitFormulaCorrectionOnePoleStandardBoundary_eq_innerSquare_of_squarePunctured_zero
        f F (le_of_lt hT)
        (zetaExplicitFormulaOnePolePunctureRadius F T)
        hsquare)
      hinner

/-- Positive-height finite Cauchy inputs for the canonical isolated `s = 1`
puncture rectangle.

This is the true finite-contour analytic sink beneath the raw standard
rectangle boundary theorem: it packages exactly the square-punctured Cauchy
cancellation and the inner-square residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalPunctureInputs_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 ∧
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
        zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          F T (zetaExplicitFormulaOnePolePunctureRadius F T) :=
    zetaCompletedExplicitFormulaCorrectionOnePole_canonicalSquarePuncturedBoundary_eq_fourCellBoundary
      f F h T hT
  have hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionOnePole_canonicalFourCellBoundary_eq_zero_of_pos_height
      f F h T hT
  have hsquare :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 :=
    Eq.trans hboundary hfour
  have hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) :=
    zetaCompletedExplicitFormulaCorrectionOnePole_canonicalInnerSquareBoundary_eq_residue_of_pos_height
      f F h T hT
  exact And.intro hsquare hinner

/-- Positive-height raw standard finite Cauchy theorem for the isolated `s = 1`
correction kernel.

This is the finite contour-residue owner theorem needed by the scheduled
left-face one-pole transport.  It keeps the honest standard-contour
normalization:
`standard boundary = 2πi * residue`, with residue
`-Phi f (1 / 2)` for the kernel `-1 / (z - 1) * Phi f (z - 1 / 2)`. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  match
    zetaCompletedExplicitFormulaCorrectionOnePole_canonicalPunctureInputs_of_pos_height
      f F h T hT with
  | ⟨hsquare, hinner⟩ =>
      exact
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_canonicalPunctureInputs
          f F h T hT hsquare hinner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
