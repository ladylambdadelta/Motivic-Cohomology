import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.StandardRectangleCauchyAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part34

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

/-- The one-pole inner square is the generic finite square boundary centered at
`1`, expressed in the same coordinate convention. -/
theorem zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral_eq_finiteRectangleSquareBoundaryIntegral_one
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R =
      finiteRectangleSquareBoundaryIntegral g (1 : ℂ) R := by
  have hone_re :
      (1 : ℂ).re = (1 : ℝ) :=
    Complex.ofReal_re 1
  have hone_im :
      (1 : ℂ).im = (0 : ℝ) :=
    Complex.ofReal_im 1
  let E : ℝ → ℝ → ℝ → ℂ :=
    fun u bottom top =>
      (∫ x : ℝ in (u - R)..(u + R),
          g (x + (((bottom : ℝ) : ℂ) * Complex.I))) -
        (∫ x : ℝ in (u - R)..(u + R),
          g (x + (((top : ℝ) : ℂ) * Complex.I))) +
          Complex.I •
            (∫ y : ℝ in bottom..top,
              g (((u + R : ℝ) : ℂ) + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in bottom..top,
                g (((u - R : ℝ) : ℂ) + y * Complex.I))
  have hcoordinate_base :
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - R) (1 + R) (-R) R =
        E 1 (-R) R :=
    Eq.refl _
  have hcenter_re :
      E 1 (-R) R = E (1 : ℂ).re (-R) R :=
    congrArg (fun u : ℝ => E u (-R) R) hone_re.symm
  have hbottom :
      -R = (1 : ℂ).im - R :=
    Eq.trans (zero_sub R).symm
      (congrArg (fun v : ℝ => v - R) hone_im.symm)
  have htop :
      R = (1 : ℂ).im + R :=
    Eq.trans (zero_add R).symm
      (congrArg (fun v : ℝ => v + R) hone_im.symm)
  have hcenter_bottom :
      E (1 : ℂ).re (-R) R =
        E (1 : ℂ).re ((1 : ℂ).im - R) R :=
    congrArg (fun bottom : ℝ => E (1 : ℂ).re bottom R) hbottom
  have hcenter_top :
      E (1 : ℂ).re ((1 : ℂ).im - R) R =
        E (1 : ℂ).re ((1 : ℂ).im - R) ((1 : ℂ).im + R) :=
    congrArg
      (fun top : ℝ => E (1 : ℂ).re ((1 : ℂ).im - R) top)
      htop
  have hcoordinate :
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - R) (1 + R) (-R) R =
        (∫ x : ℝ in ((1 : ℂ).re - R)..((1 : ℂ).re + R),
            g (x + ((((1 : ℂ).im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in ((1 : ℂ).re - R)..((1 : ℂ).re + R),
            g (x + ((((1 : ℂ).im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in ((1 : ℂ).im - R)..((1 : ℂ).im + R),
                g (((((1 : ℂ).re + R : ℝ) : ℂ)) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in ((1 : ℂ).im - R)..((1 : ℂ).im + R),
                  g (((((1 : ℂ).re - R : ℝ) : ℂ)) + y * Complex.I)) :=
    Eq.trans hcoordinate_base
      (Eq.trans hcenter_re (Eq.trans hcenter_bottom hcenter_top))
  calc
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (1 - R) (1 + R) (-R) R := by
      exact zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral_eq g R
    _ =
        (∫ x : ℝ in ((1 : ℂ).re - R)..((1 : ℂ).re + R),
            g (x + ((((1 : ℂ).im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in ((1 : ℂ).re - R)..((1 : ℂ).re + R),
            g (x + ((((1 : ℂ).im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in ((1 : ℂ).im - R)..((1 : ℂ).im + R),
                g (((((1 : ℂ).re + R : ℝ) : ℂ)) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in ((1 : ℂ).im - R)..((1 : ℂ).im + R),
                  g (((((1 : ℂ).re - R : ℝ) : ℂ)) + y * Complex.I)) := hcoordinate
    _ = finiteRectangleSquareBoundaryIntegral g (1 : ℂ) R :=
      (finiteRectangleSquareBoundaryIntegral_eq g (1 : ℂ) R).symm

/-- The residue coefficient `(z - 1) g(z)` of the one-pole correction kernel is
continuous on every set with the pole removed. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCoefficient_continuousOn_deletedSet
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (s : Set ℂ) :
    ContinuousOn
      (fun z : ℂ =>
        (z - 1) * zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (s \ ({(1 : ℂ)} : Set ℂ)) := by
  intro z hz
  have hz_not_mem : z ∉ ({(1 : ℂ)} : Set ℂ) :=
    hz.2
  have hz_ne : z - 1 ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 :=
      sub_eq_zero.mp hzero
    have hz_mem : z ∈ ({(1 : ℂ)} : Set ℂ) :=
      hz_eq
    exact hz_not_mem hz_mem
  have hleft :
      ContinuousAt (fun w : ℂ => w - 1) z :=
    (continuous_id.sub continuous_const).continuousAt
  have hright :
      ContinuousAt
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_continuousAt_off_pole
      f hPhi hz_ne
  exact (hleft.mul hright).continuousWithinAt

/-- The residue coefficient `(z - 1) g(z)` of the one-pole correction kernel is
differentiable away from the removed singleton. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_deletedCoefficient_differentiableAt_of_not_mem_singleton
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    {z : ℂ} (hz : z ∉ ({(1 : ℂ)} : Set ℂ)) :
    DifferentiableAt ℂ
      (fun w : ℂ =>
        (w - 1) * zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
      z := by
  have hz_ne : z - 1 ≠ 0 := by
    intro hzero
    have hz_eq : z = 1 :=
      sub_eq_zero.mp hzero
    have hz_mem : z ∈ ({(1 : ℂ)} : Set ℂ) :=
      hz_eq
    exact hz hz_mem
  have hleft :
      DifferentiableAt ℂ (fun w : ℂ => w - 1) z :=
    differentiableAt_id.sub (differentiableAt_const (1 : ℂ))
  have hright :
      DifferentiableAt ℂ
        (fun w : ℂ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
        z :=
    zetaCompletedExplicitFormulaCorrectionOnePoleKernel_differentiableAt_off_pole
      f hPhi hz_ne
  exact hleft.mul hright

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

/-- Canonical inner-square residue value for the isolated `s = 1` correction
kernel at positive height.  This is the local square-boundary residue transport
for the canonical puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePole_canonicalInnerSquareBoundary_eq_residue_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (T : ℝ)
    (hT : 0 < T) :
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
  have hR :
      0 < zetaExplicitFormulaOnePolePunctureRadius F T :=
    zetaCompletedExplicitFormulaCorrectionOnePole_punctureRadius_pos_of_pos_height
      F hT
  have hinner_square :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (zetaExplicitFormulaOnePolePunctureRadius F T) =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (1 : ℂ)
          (zetaExplicitFormulaOnePolePunctureRadius F T) :=
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral_eq_finiteRectangleSquareBoundaryIntegral_one
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (zetaExplicitFormulaOnePolePunctureRadius F T)
  have hcontinuous :
      ContinuousOn
        (fun z : ℂ =>
          (z - (1 : ℂ)) *
            zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        ((Set.uIcc
            ((1 : ℂ).re - zetaExplicitFormulaOnePolePunctureRadius F T)
            ((1 : ℂ).re + zetaExplicitFormulaOnePolePunctureRadius F T) ×ℂ
          Set.uIcc
            ((1 : ℂ).im - zetaExplicitFormulaOnePolePunctureRadius F T)
            ((1 : ℂ).im + zetaExplicitFormulaOnePolePunctureRadius F T)) \
            ({(1 : ℂ)} : Set ℂ)) :=
    zetaCompletedExplicitFormulaCorrectionOnePole_deletedCoefficient_continuousOn_deletedSet
      f h.phi_control
      (Set.uIcc
        ((1 : ℂ).re - zetaExplicitFormulaOnePolePunctureRadius F T)
        ((1 : ℂ).re + zetaExplicitFormulaOnePolePunctureRadius F T) ×ℂ
        Set.uIcc
          ((1 : ℂ).im - zetaExplicitFormulaOnePolePunctureRadius F T)
          ((1 : ℂ).im + zetaExplicitFormulaOnePolePunctureRadius F T))
  have hdifferentiable :
      ∀ z : ℂ,
        z ∈
            ((Set.Ioo
                  ((1 : ℂ).re - zetaExplicitFormulaOnePolePunctureRadius F T)
                  ((1 : ℂ).re + zetaExplicitFormulaOnePolePunctureRadius F T) ×ℂ
                Set.Ioo
                  ((1 : ℂ).im - zetaExplicitFormulaOnePolePunctureRadius F T)
                  ((1 : ℂ).im + zetaExplicitFormulaOnePolePunctureRadius F T)) \
                ({(1 : ℂ)} : Set ℂ)) \ (∅ : Set ℂ) →
          DifferentiableAt ℂ
            (fun w : ℂ =>
              (w - (1 : ℂ)) *
                zetaCompletedExplicitFormulaCorrectionOnePoleKernel f w)
            z := by
    intro z hz
    exact
      zetaCompletedExplicitFormulaCorrectionOnePole_deletedCoefficient_differentiableAt_of_not_mem_singleton
        f h.phi_control hz.1.2
  have hfinite_square :
      finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (1 : ℂ)
          (zetaExplicitFormulaOnePolePunctureRadius F T) =
        (2 * (Real.pi : ℂ) * Complex.I) •
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) :=
    finiteRectangleSquareBoundaryIntegral_eq_twoPiI_smul_residue
      (1 : ℂ) hR
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
      (∅ : Set ℂ)
      Set.countable_empty
      hcontinuous
      hdifferentiable
      (zetaCompletedExplicitFormulaCorrectionOnePoleKernel_localResidue_tendsto
        f h.phi_control)
  calc
    zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
        (zetaExplicitFormulaOnePolePunctureRadius F T) =
        finiteRectangleSquareBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionOnePoleKernel f z)
          (1 : ℂ)
          (zetaExplicitFormulaOnePolePunctureRadius F T) := hinner_square
    _ = (2 * (Real.pi : ℂ) * Complex.I) •
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := hfinite_square
    _ = (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)) := by
      exact
        Algebra.id.smul_eq_mul
          (2 * (Real.pi : ℂ) * Complex.I)
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
