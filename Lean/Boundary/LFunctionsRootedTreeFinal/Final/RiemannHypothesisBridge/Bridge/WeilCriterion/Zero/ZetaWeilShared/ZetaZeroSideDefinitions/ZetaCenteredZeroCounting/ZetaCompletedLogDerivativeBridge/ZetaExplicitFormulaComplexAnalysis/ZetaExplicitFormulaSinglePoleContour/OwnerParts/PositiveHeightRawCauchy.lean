import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.StandardRectangleCauchyAssembly

/-!
# Positive-height raw Cauchy assembly for the isolated `s = 1` correction pole

This file owns the final finite-height assembly layer for the isolated one-pole
correction kernel.  The theorem names the three geometric inputs that remain
upstream:

* the square-punctured rectangle boundary decomposes as the four-cell boundary;
* the four-cell boundary vanishes by Cauchy-Goursat away from the pole;
* the inner square boundary carries the local residue.

The vertical-channel owner should only consume this finite raw theorem, not
rebuild the contour argument.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The canonical one-pole puncture radius attached to a positive-height
rectangle is positive.  This is the radius used by the finite raw Cauchy
assembly below. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
  zetaExplicitFormulaOnePolePunctureRadius_pos F hT

/-- A positive-height contour has nonnegative height, in the exact form needed
by the standard-boundary coordinate transport theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_height_nonneg_of_pos_height
    {T : ℝ} (hT : 0 < T) :
    0 ≤ T :=
  le_of_lt hT

/-- The canonical one-pole puncture radius is strictly inside the right
horizontal margin of a positive-height contour. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_lt_rightMargin_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < F.c - 1 :=
  zetaExplicitFormulaOnePolePunctureRadius_lt_rightMargin F hT

/-- The canonical one-pole puncture radius is strictly inside the left
horizontal margin of a positive-height contour. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_lt_leftMargin_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < F.c :=
  zetaExplicitFormulaOnePolePunctureRadius_lt_leftMargin F hT

/-- The canonical one-pole puncture radius is strictly below the contour height. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_lt_height_of_pos_height
    (F : ExplicitFormulaContourFamily) {T : ℝ} (hT : 0 < T) :
    zetaExplicitFormulaOnePolePunctureRadius F T < T :=
  zetaExplicitFormulaOnePolePunctureRadius_lt_height F hT

/-- The finite square-punctured rectangle boundary at the canonical one-pole
puncture radius vanishes once it is identified with the four-cell boundary and
the four-cell boundary has zero Cauchy-Goursat sum. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_squarePuncturedBoundary_eq_zero_of_fourCellBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T))
    (hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      F T (zetaExplicitFormulaOnePolePunctureRadius F T) = 0 :=
  Eq.trans hboundary hfour

/-- Positive-height raw standard Cauchy assembly at the canonical one-pole
puncture radius.  The three inputs are exactly the owner facts supplied by the
finite contour argument: boundary decomposition, four-cell Cauchy cancellation,
and the inner-square residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_geometric_inputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hT : 0 < T)
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T))
    (hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
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
  have hT_nonneg :
      0 ≤ T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_height_nonneg_of_pos_height
      hT
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_fourCellBoundary_and_innerSquare
      f F hT_nonneg hboundary hfour hinner

/-- Positive-height raw standard Cauchy assembly from square-punctured
cancellation and the inner-square residue value at the canonical one-pole
puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_squarePunctured
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
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
  have hT_nonneg :
      0 ≤ T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_height_nonneg_of_pos_height
      hT
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_squarePunctured_zero_and_innerSquare
      f F hT_nonneg hsquare hinner

/-- The same positive-height assembly with an explicitly named inner-square
radius.  This form is convenient for proofs that first establish radius
geometry and then feed that radius into the contour bookkeeping. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_radius_inputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hT : 0 < T)
    (R : ℝ)
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
  have hT_nonneg :
      0 ≤ T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_height_nonneg_of_pos_height
      hT
  exact
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_fourCellBoundary_and_innerSquare
      f F hT_nonneg hboundary hfour hinner

/-- The canonical puncture radius form follows from the named-radius form by
taking the radius to be definitionally the canonical one. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_canonical_punctureRadius_inputs
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T : ℝ}
    (hT : 0 < T)
    (hboundary :
      zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T) =
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        F T (zetaExplicitFormulaOnePolePunctureRadius F T))
    (hfour :
      zetaExplicitFormulaOnePoleFourCellPuncturedRectangleBoundarySum
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
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_radius_inputs
      f F hT (zetaExplicitFormulaOnePolePunctureRadius F T)
      hboundary hfour hinner

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
