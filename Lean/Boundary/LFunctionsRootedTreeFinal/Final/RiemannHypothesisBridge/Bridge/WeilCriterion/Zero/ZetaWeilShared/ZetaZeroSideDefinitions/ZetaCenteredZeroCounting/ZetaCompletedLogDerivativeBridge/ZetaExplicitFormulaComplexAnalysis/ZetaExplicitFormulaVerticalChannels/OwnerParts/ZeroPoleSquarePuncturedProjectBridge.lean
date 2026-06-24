import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedSplits
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.PoleKernelVerticalInversion

/-!
# Project bridge for the zero-pole square-punctured boundary

This file compares the project-specific zero-pole correction boundary from
`CorrectionPoleResidues` with the generic zero-centered square-punctured
rectangle boundary supplied by the four-cell contour owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology Interval

namespace ZetaAdmissibleFunction

/-- The bottom path convention used by the project contour is the same affine
coordinate path used by the generic rectangle boundary. -/
theorem zetaCompletedExplicitFormulaBottomPath_eq_zeroPole_outerBottomAffine
    (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x =
      (x : ℂ) + (-T : ℝ) * Complex.I := by
  calc
    zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x =
        (x : ℂ) - (T : ℂ) * Complex.I := by
      rfl
    _ = (x : ℂ) + -((T : ℂ) * Complex.I) := by
      exact sub_eq_add_neg (x : ℂ) ((T : ℂ) * Complex.I)
    _ = (x : ℂ) + ((-(T : ℂ)) * Complex.I) := by
      exact congrArg (fun z : ℂ => (x : ℂ) + z)
        (neg_mul (T : ℂ) Complex.I).symm
    _ = (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I := by
      exact congrArg
        (fun z : ℂ => (x : ℂ) + z * Complex.I)
        (Complex.ofReal_neg T).symm

/-- The top path convention used by the project contour is the generic top
affine coordinate path. -/
theorem zetaCompletedExplicitFormulaTopPath_eq_zeroPole_outerTopAffine
    (F : ExplicitFormulaContourFamily) (T x : ℝ) :
    zetaCompletedExplicitFormulaTopPath (F.rectangle T) x =
      (x : ℂ) + (T : ℝ) * Complex.I := by
  rfl

/-- The right path convention used by the project contour is the generic right
vertical affine coordinate path. -/
theorem zetaCompletedExplicitFormulaRightPath_eq_zeroPole_outerRightAffine
    (F : ExplicitFormulaContourFamily) (T y : ℝ) :
    zetaCompletedExplicitFormulaRightPath (F.rectangle T) y =
      (F.c : ℂ) + y * Complex.I := by
  rfl

/-- The left path convention used by the project contour is the generic left
vertical affine coordinate path. -/
theorem zetaCompletedExplicitFormulaLeftPath_eq_zeroPole_outerLeftAffine
    (F : ExplicitFormulaContourFamily) (T y : ℝ) :
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) y =
      ((1 - F.c : ℝ) : ℂ) + y * Complex.I := by
  rfl

/-- The project bottom integral is the generic zero-pole outer bottom edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectBottom_eq_outerBottomEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) =
      zetaExplicitFormulaZeroPoleOuterBottomEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  have hintegrand :
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) =
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          ((x : ℂ) + (-T : ℝ) * Complex.I)) := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      (zetaCompletedExplicitFormulaBottomPath_eq_zeroPole_outerBottomAffine F T x)
  calc
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) =
        ∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + (-T : ℝ) * Complex.I) := by
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ x in Set.Icc (1 - F.c) F.c, φ x)
        hintegrand
    _ =
      zetaExplicitFormulaZeroPoleOuterBottomEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      rfl

/-- The project top integral is the generic zero-pole outer top edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectTop_eq_outerTopEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) =
      zetaExplicitFormulaZeroPoleOuterTopEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  rfl

/-- The project right tangent side is the generic zero-pole outer right edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectRight_eq_outerRightEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
      zetaExplicitFormulaZeroPoleOuterRightEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  calc
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
        ∫ y in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaRightPath (F.rectangle T) y) *
              Complex.I := by
      rfl
    _ =
        ∫ y in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((F.c : ℂ) + y * Complex.I) * Complex.I := by
      rfl
    _ =
      zetaExplicitFormulaZeroPoleOuterRightEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      exact
        (integral_smul_const
          (μ := volume.restrict (Set.Icc (-T) T))
          (fun y : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
              ((F.c : ℂ) + y * Complex.I))
          Complex.I).symm

/-- The project left tangent side is the generic zero-pole outer left edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectLeft_eq_outerLeftEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
      zetaExplicitFormulaZeroPoleOuterLeftEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  calc
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
        ∫ y in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) y) *
              Complex.I := by
      rfl
    _ =
        ∫ y in Set.Icc (-T) T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I) * Complex.I := by
      rfl
    _ =
      zetaExplicitFormulaZeroPoleOuterLeftEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      exact
        (integral_smul_const
          (μ := volume.restrict (Set.Icc (-T) T))
          (fun y : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
              (((1 - F.c : ℝ) : ℂ) + y * Complex.I))
          Complex.I).symm

/-- The project standard zero-pole boundary is the generic zero-pole outer
standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_outerStandard
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T =
      zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  let g : ℂ → ℂ := fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z
  let B : ℂ := zetaExplicitFormulaZeroPoleOuterBottomEdge g F T
  let U : ℂ := zetaExplicitFormulaZeroPoleOuterTopEdge g F T
  let R : ℂ := zetaExplicitFormulaZeroPoleOuterRightEdge g F T
  let L : ℂ := zetaExplicitFormulaZeroPoleOuterLeftEdge g F T
  have hbottom :
      (∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) = B :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectBottom_eq_outerBottomEdge
      f F T
  have htop :
      (∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) = U :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectTop_eq_outerTopEdge
      f F T
  have hright :
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T = R :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectRight_eq_outerRightEdge
      f F T
  have hleft :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T = L :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectLeft_eq_outerLeftEdge
      f F T
  have hgeneric :
      zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T =
        B - U + (R - L) :=
    zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral_eq_namedEdges
      g F T
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T =
        (∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x)) -
          (∫ x in Set.Icc (1 - F.c) F.c,
            zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
              (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) +
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T -
              zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T := by
      rfl
    _ = B - U + R - L := by
      exact congrArg₂ HSub.hSub
        (congrArg₂ HAdd.hAdd
          (congrArg₂ HSub.hSub hbottom htop)
          hright)
        hleft
    _ = B - U + (R - L) := by
      exact (sub_eq_add_neg (B - U + R) L).trans
        (congrArg (fun z : ℂ => B - U + z) (sub_eq_add_neg R L).symm)
    _ =
      zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T := by
      exact hgeneric.symm

/-- The generic zero-pole inner square boundary is the finite rectangle square
boundary centered at zero. -/
theorem zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral_eq_finiteRectangleSquareBoundaryIntegral_zero
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
      finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
  calc
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (-R) R (-R) R := by
      rfl
    _ =
      finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
      exact (finiteRectangleSquareBoundaryIntegral_eq g (0 : ℂ) R).symm

/-- The project zero-pole square-punctured boundary is the generic zero-centered
square-punctured rectangle boundary for the correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral_eq_generic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R =
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T R := by
  let g : ℂ → ℂ := fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z
  have houter :
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T =
        zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_outerStandard
      f F T
  have hinner :
      finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R =
        zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R :=
    (zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral_eq_finiteRectangleSquareBoundaryIntegral_zero
      g R).symm
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R =
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral f F T -
          finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
      rfl
    _ =
        zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T -
          finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
      exact congrArg
        (fun z : ℂ => z - finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R)
        houter
    _ =
        zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T -
          zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R := by
      exact congrArg
        (fun z : ℂ =>
          zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T - z)
        hinner
    _ =
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R := by
      rfl

/-- Positive-height cancellation of the project-specific zero-pole
square-punctured boundary at the canonical puncture radius. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectSquarePuncturedBoundary_eq_zero_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  let g : ℂ → ℂ := fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z
  have hgeneric :
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_zero_of_pos_height
      f F hPhi hT
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R =
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral_eq_generic
        f F T R
    _ = 0 := hgeneric

/-- Positive-height raw Cauchy theorem for the project-specific zero-pole
standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hcauchy :
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
          f F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectSquarePuncturedBoundary_eq_zero_of_pos_height
      f F hPhi hT
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_canonicalSquarePunctured_zero
      f F hPhi hT hcauchy

/-- Positive-height raw standard-contour Cauchy theorem for the isolated
zero-pole local tangent residue, using the named local-residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_localTangentResidueValue_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T : ℝ} (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f := by
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
        f F T =
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
      exact
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F hPhi hT
    _ =
        zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f := by
      exact
        (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue_eq
          f).symm

/-- Scheduled normalized zero-pole boundary residue value, obtained from the
positive-height project square-punctured Cauchy theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_normalizedStandardBoundaryResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∀ᶠ u in atTop,
      zetaCompletedExplicitFormulaCorrectionZeroPoleNormalizedStandardRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        -zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)) :=
  zetaCompletedExplicitFormulaCorrectionZeroPole_eventually_normalizedStandardBoundaryResidueValue_of_positiveHeight_rawCauchy
    f F h
    (fun T hT =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
        f F h.phi_control hT)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
