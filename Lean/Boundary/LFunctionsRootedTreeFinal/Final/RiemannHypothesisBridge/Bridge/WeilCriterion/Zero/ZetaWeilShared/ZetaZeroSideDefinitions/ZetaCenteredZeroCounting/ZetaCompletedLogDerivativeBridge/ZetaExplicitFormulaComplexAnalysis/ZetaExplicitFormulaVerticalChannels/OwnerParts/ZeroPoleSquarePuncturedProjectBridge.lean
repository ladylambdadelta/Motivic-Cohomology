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

/-- On an ordered real interval, the set integral over `Icc` is the corresponding
oriented interval integral. -/
theorem zetaExplicitFormula_setIntegral_Icc_eq_intervalIntegral_of_le
    (φ : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Icc a b, φ x) = ∫ x : ℝ in a..b, φ x := by
  have hIccIoc :
      (∫ x in Set.Icc a b, φ x) = ∫ x in Set.Ioc a b, φ x :=
    MeasureTheory.integral_Icc_eq_integral_Ioc
  have hInterval :
      (∫ x : ℝ in a..b, φ x) = ∫ x in Set.Ioc a b, φ x :=
    intervalIntegral.integral_of_le hab
  exact Eq.trans hIccIoc hInterval.symm

/-- The zero-pole contour family's horizontal projection interval is ordered. -/
theorem zetaExplicitFormulaZeroPole_one_sub_c_le_c
    (F : ExplicitFormulaContourFamily) :
    1 - F.c ≤ F.c :=
  (le_of_lt F.one_sub_c_neg).trans (le_of_lt F.c_pos)

/-- A nonnegative height gives the ordered vertical interval `[-T,T]`. -/
theorem zetaExplicitFormulaZeroPole_neg_height_le_height
    {T : ℝ} (hT : 0 ≤ T) :
    -T ≤ T :=
  (neg_nonpos.mpr hT).trans hT

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
  calc
    zetaCompletedExplicitFormulaLeftPath (F.rectangle T) y =
        (1 : ℂ) - (F.c : ℂ) + y * Complex.I := by
      rfl
    _ = ((1 - F.c : ℝ) : ℂ) + y * Complex.I := by
      exact congrArg
        (fun z : ℂ => z + y * Complex.I)
        (Complex.ofReal_sub (1 : ℝ) F.c).symm

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
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + (-T : ℝ) * Complex.I) := by
      exact zetaExplicitFormula_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + (-T : ℝ) * Complex.I))
        (zetaExplicitFormulaZeroPole_one_sub_c_le_c F)
    _ =
      zetaExplicitFormulaZeroPoleOuterBottomEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      unfold zetaExplicitFormulaZeroPoleOuterBottomEdge
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
  have hintegrand :
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) =
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
          ((x : ℂ) + T * Complex.I)) := by
    funext x
    exact congrArg
      (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
      (zetaCompletedExplicitFormulaTopPath_eq_zeroPole_outerTopAffine F T x)
  calc
    (∫ x in Set.Icc (1 - F.c) F.c,
      zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x)) =
        ∫ x in Set.Icc (1 - F.c) F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + T * Complex.I) := by
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ x in Set.Icc (1 - F.c) F.c, φ x)
        hintegrand
    _ =
        ∫ x : ℝ in (1 - F.c)..F.c,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + T * Complex.I) := by
      exact zetaExplicitFormula_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun x : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((x : ℂ) + T * Complex.I))
        (zetaExplicitFormulaZeroPole_one_sub_c_le_c F)
    _ =
      zetaExplicitFormulaZeroPoleOuterTopEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      unfold zetaExplicitFormulaZeroPoleOuterTopEdge
      rfl

/-- The project right tangent side is the generic zero-pole outer right edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectRight_eq_outerRightEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleTangentIntegral f F T =
      zetaExplicitFormulaZeroPoleOuterRightEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  let φ : ℝ → ℂ := fun y : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      ((F.c : ℂ) + y * Complex.I)
  have hheight : -T ≤ T :=
    zetaExplicitFormulaZeroPole_neg_height_le_height hT
  have hmul :
      (∫ y : ℝ in -T..T, φ y * Complex.I) =
        (∫ y : ℝ in -T..T, φ y) * Complex.I :=
    intervalIntegral.integral_mul_const Complex.I φ
  have hcomm :
      (∫ y : ℝ in -T..T, φ y) * Complex.I =
        Complex.I • (∫ y : ℝ in -T..T, φ y) :=
    mul_comm (∫ y : ℝ in -T..T, φ y) Complex.I
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
        ∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((F.c : ℂ) + y * Complex.I) * Complex.I := by
      exact zetaExplicitFormula_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((F.c : ℂ) + y * Complex.I) * Complex.I)
        hheight
    _ =
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((F.c : ℂ) + y * Complex.I)) * Complex.I := by
      exact hmul
    _ =
        Complex.I • (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            ((F.c : ℂ) + y * Complex.I)) := by
      exact hcomm
    _ =
      zetaExplicitFormulaZeroPoleOuterRightEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      unfold zetaExplicitFormulaZeroPoleOuterRightEdge
      rfl

/-- The project left tangent side is the generic zero-pole outer left edge. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPole_projectLeft_eq_outerLeftEdge
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T =
      zetaExplicitFormulaZeroPoleOuterLeftEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
  let φ : ℝ → ℂ := fun y : ℝ =>
    zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
      (((1 - F.c : ℝ) : ℂ) + y * Complex.I)
  have hheight : -T ≤ T :=
    zetaExplicitFormulaZeroPole_neg_height_le_height hT
  have hmul :
      (∫ y : ℝ in -T..T, φ y * Complex.I) =
        (∫ y : ℝ in -T..T, φ y) * Complex.I :=
    intervalIntegral.integral_mul_const Complex.I φ
  have hcomm :
      (∫ y : ℝ in -T..T, φ y) * Complex.I =
        Complex.I • (∫ y : ℝ in -T..T, φ y) :=
    mul_comm (∫ y : ℝ in -T..T, φ y) Complex.I
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
      exact congrArg
        (fun φ : ℝ → ℂ => ∫ y in Set.Icc (-T) T, φ y * Complex.I)
        (by
          funext y
          exact congrArg
            (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
            (zetaCompletedExplicitFormulaLeftPath_eq_zeroPole_outerLeftAffine F T y))
    _ =
        ∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I) * Complex.I := by
      exact zetaExplicitFormula_setIntegral_Icc_eq_intervalIntegral_of_le
        (fun y : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I) * Complex.I)
        hheight
    _ =
        (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) * Complex.I := by
      exact hmul
    _ =
        Complex.I • (∫ y : ℝ in -T..T,
          zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f
            (((1 - F.c : ℝ) : ℂ) + y * Complex.I)) := by
      exact hcomm
    _ =
      zetaExplicitFormulaZeroPoleOuterLeftEdge
        (fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z)
        F T := by
      unfold zetaExplicitFormulaZeroPoleOuterLeftEdge
      rfl

/-- The project standard zero-pole boundary is the generic zero-pole outer
standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_outerStandard
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T : ℝ}
    (hT : 0 ≤ T) :
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
      f F hT
  have hleft :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleTangentIntegral f F T = L :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectLeft_eq_outerLeftEdge
      f F hT
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
      have hsub :
          B - U + R - L = (B - U + R) + -L :=
        sub_eq_add_neg (B - U + R) L
      have hassoc :
          (B - U + R) + -L = B - U + (R + -L) :=
        add_assoc (B - U) R (-L)
      have hinner :
          B - U + (R + -L) = B - U + (R - L) :=
        congrArg (fun z : ℂ => B - U + z) (sub_eq_add_neg R L).symm
      exact Eq.trans hsub (Eq.trans hassoc hinner)
    _ =
      zetaExplicitFormulaZeroPoleOuterStandardBoundaryCoordinateIntegral g F T := by
      exact hgeneric.symm

/-- The generic zero-pole inner square boundary is the finite rectangle square
boundary centered at zero. -/
theorem zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral_eq_finiteRectangleSquareBoundaryIntegral_zero
    (g : ℂ → ℂ) (R : ℝ) :
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
      finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
  have hzero_re :
      (0 : ℂ).re = (0 : ℝ) :=
    Complex.zero_re
  have hzero_im :
      (0 : ℂ).im = (0 : ℝ) :=
    Complex.zero_im
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
  let A : ℝ → ℝ → ℝ → ℝ → ℂ :=
    fun left right bottom top =>
      (∫ x : ℝ in left..right,
          g (x + (((bottom : ℝ) : ℂ) * Complex.I))) -
        (∫ x : ℝ in left..right,
          g (x + (((top : ℝ) : ℂ) * Complex.I))) +
          Complex.I •
            (∫ y : ℝ in bottom..top,
              g (((right : ℝ) : ℂ) + y * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in bottom..top,
                g (((left : ℝ) : ℂ) + y * Complex.I))
  have hleft_zero :
      -R = (0 : ℝ) - R :=
    (zero_sub R).symm
  have hright_zero :
      R = (0 : ℝ) + R :=
    (zero_add R).symm
  have hcoordinate_standard :
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (-R) R (-R) R =
        A (-R) R (-R) R :=
    Eq.refl _
  have hcoordinate_left :
      A (-R) R (-R) R =
        A ((0 : ℝ) - R) R (-R) R :=
    congrArg (fun left : ℝ => A left R (-R) R) hleft_zero
  have hcoordinate_right :
      A ((0 : ℝ) - R) R (-R) R =
        A ((0 : ℝ) - R) ((0 : ℝ) + R) (-R) R :=
    congrArg (fun right : ℝ => A ((0 : ℝ) - R) right (-R) R) hright_zero
  have hcoordinate_base :
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (-R) R (-R) R =
        E 0 (-R) R :=
    Eq.trans hcoordinate_standard
      (Eq.trans hcoordinate_left hcoordinate_right)
  have hcenter_re :
      E 0 (-R) R = E (0 : ℂ).re (-R) R :=
    congrArg (fun u : ℝ => E u (-R) R) hzero_re.symm
  have hbottom :
      -R = (0 : ℂ).im - R :=
    Eq.trans (zero_sub R).symm
      (congrArg (fun v : ℝ => v - R) hzero_im.symm)
  have htop :
      R = (0 : ℂ).im + R :=
    Eq.trans (zero_add R).symm
      (congrArg (fun v : ℝ => v + R) hzero_im.symm)
  have hcenter_bottom :
      E (0 : ℂ).re (-R) R =
        E (0 : ℂ).re ((0 : ℂ).im - R) R :=
    congrArg (fun bottom : ℝ => E (0 : ℂ).re bottom R) hbottom
  have hcenter_top :
      E (0 : ℂ).re ((0 : ℂ).im - R) R =
        E (0 : ℂ).re ((0 : ℂ).im - R) ((0 : ℂ).im + R) :=
    congrArg
      (fun top : ℝ => E (0 : ℂ).re ((0 : ℂ).im - R) top)
      htop
  have hcoordinate :
      zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (-R) R (-R) R =
        (∫ x : ℝ in ((0 : ℂ).re - R)..((0 : ℂ).re + R),
            g (x + ((((0 : ℂ).im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in ((0 : ℂ).re - R)..((0 : ℂ).re + R),
            g (x + ((((0 : ℂ).im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in ((0 : ℂ).im - R)..((0 : ℂ).im + R),
                g (((((0 : ℂ).re + R : ℝ) : ℂ)) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in ((0 : ℂ).im - R)..((0 : ℂ).im + R),
                  g (((((0 : ℂ).re - R : ℝ) : ℂ)) + y * Complex.I)) :=
    Eq.trans hcoordinate_base
      (Eq.trans hcenter_re (Eq.trans hcenter_bottom hcenter_top))
  calc
    zetaExplicitFormulaZeroPoleInnerSquareBoundaryIntegral g R =
        zetaExplicitFormulaSinglePoleStandardRectangleBoundaryCoordinateIntegral
          g (-R) R (-R) R := by
      rfl
    _ =
        (∫ x : ℝ in ((0 : ℂ).re - R)..((0 : ℂ).re + R),
            g (x + ((((0 : ℂ).im - R : ℝ) : ℂ) * Complex.I))) -
          (∫ x : ℝ in ((0 : ℂ).re - R)..((0 : ℂ).re + R),
            g (x + ((((0 : ℂ).im + R : ℝ) : ℂ) * Complex.I))) +
            Complex.I •
              (∫ y : ℝ in ((0 : ℂ).im - R)..((0 : ℂ).im + R),
                g (((((0 : ℂ).re + R : ℝ) : ℂ)) + y * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in ((0 : ℂ).im - R)..((0 : ℂ).im + R),
                  g (((((0 : ℂ).re - R : ℝ) : ℂ)) + y * Complex.I)) :=
      hcoordinate
    _ =
      finiteRectangleSquareBoundaryIntegral g (0 : ℂ) R := by
      exact (finiteRectangleSquareBoundaryIntegral_eq g (0 : ℂ) R).symm

/-- The project zero-pole square-punctured boundary is the generic zero-centered
square-punctured rectangle boundary for the correction kernel. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral_eq_generic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) {T R : ℝ}
    (hT : 0 ≤ T) :
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
      f F hT
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
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 := by
  let R : ℝ := zetaExplicitFormulaZeroPolePunctureRadius F T
  let g : ℂ → ℂ := fun z : ℂ => zetaCompletedExplicitFormulaCorrectionZeroPoleKernel f z
  have hgeneric :
    zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_canonicalSquarePuncturedBoundary_eq_zero_of_pos_height
      f F h T hT
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
        f F T R =
      zetaExplicitFormulaZeroPoleSquarePuncturedRectangleBoundaryIntegral g F T R :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral_eq_generic
        f F (le_of_lt hT)
    _ = 0 := hgeneric

/-- Positive-height raw Cauchy theorem for the project-specific zero-pole
standard rectangle boundary. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
      f F T =
      (2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))) := by
  have hcauchy :
    zetaCompletedExplicitFormulaCorrectionZeroPoleSquarePuncturedBoundaryIntegral
          f F T (zetaExplicitFormulaZeroPolePunctureRadius F T) = 0 :=
    zetaCompletedExplicitFormulaCorrectionZeroPole_projectSquarePuncturedBoundary_eq_zero_of_pos_height
      f F h hT
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height_canonicalSquarePunctured_zero
      f F h.phi_control hT hcauchy

/-- Positive-height raw standard-contour Cauchy theorem for the isolated
zero-pole local tangent residue, using the named local-residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_localTangentResidueValue_of_pos_height
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T : ℝ} (hT : 0 < T) :
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
          f F h hT
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
    (fun _T hT =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
        f F h hT)

end ZetaAdmissibleFunction

end

end LFunctions
end Boundary
