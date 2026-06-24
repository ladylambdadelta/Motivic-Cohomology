import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.CorrectionPoleResidues

/-!
# Zero-pole tangent-boundary algebra

This file owns the non-analytic algebra that relates the genuine tangent
zero-pole boundary defect to the left zero-pole face and the isolated
horizontal remainder.  It deliberately does not import the right zero-pole
transport stack, so it can be used upstream of the isolated pole Cauchy
inversion theorem.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Solve the corrected tangent-contour boundary identity for the scheduled
left `s = 0` vertical face.  This is pure orientation algebra. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I_ownerZeroPoleAlgebra
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hC : C = R * Complex.I - L * Complex.I + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F h u
  have hI_mul_I : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  have hC_mul_I :
      C * Complex.I = -R + L + H * Complex.I := by
    calc
      C * Complex.I = (R * Complex.I - L * Complex.I + H) * Complex.I := by
        exact congrArg (fun x : ℂ => x * Complex.I) hC
      _ = ((R * Complex.I - L * Complex.I) + H) * Complex.I := by
        rfl
      _ = (R * Complex.I - L * Complex.I) * Complex.I + H * Complex.I := by
        exact add_mul (R * Complex.I - L * Complex.I) H Complex.I
      _ = ((R * Complex.I) + -(L * Complex.I)) * Complex.I + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => x * Complex.I + H * Complex.I)
          (sub_eq_add_neg (R * Complex.I) (L * Complex.I))
      _ =
          ((R * Complex.I) * Complex.I + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => x + H * Complex.I)
          (add_mul (R * Complex.I) (-(L * Complex.I)) Complex.I)
      _ =
          (R * (Complex.I * Complex.I) + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * Complex.I) + H * Complex.I)
          (mul_assoc R Complex.I Complex.I)
      _ =
          (R * (-(1 : ℂ)) + (-(L * Complex.I)) * Complex.I) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * Complex.I) + H * Complex.I)
          hI_mul_I
      _ =
          (R * (-(1 : ℂ)) + -((L * Complex.I) * Complex.I)) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + x) + H * Complex.I)
          (neg_mul (L * Complex.I) Complex.I)
      _ =
          (R * (-(1 : ℂ)) + -(L * (Complex.I * Complex.I))) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + -x) + H * Complex.I)
          (mul_assoc L Complex.I Complex.I)
      _ =
          (R * (-(1 : ℂ)) + -(L * (-(1 : ℂ)))) +
            H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (R * (-(1 : ℂ)) + -(L * x)) + H * Complex.I)
          hI_mul_I
      _ = (-R + -(L * (-(1 : ℂ)))) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (x + -(L * (-(1 : ℂ)))) + H * Complex.I)
          (mul_neg_one R)
      _ = (-R + -(-L)) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (-R + -x) + H * Complex.I)
          (mul_neg_one L)
      _ = (-R + L) + H * Complex.I := by
        exact congrArg
          (fun x : ℂ => (-R + x) + H * Complex.I)
          (neg_neg L)
      _ = -R + L + H * Complex.I := by
        rfl
  have hsolve :
      L = R + C * Complex.I - H * Complex.I := by
    have hstep :
        C * Complex.I - H * Complex.I = -R + L := by
      calc
        C * Complex.I - H * Complex.I =
            (-R + L + H * Complex.I) - H * Complex.I := by
          exact congrArg (fun x : ℂ => x - H * Complex.I) hC_mul_I
        _ = ((-R + L) + H * Complex.I) + -(H * Complex.I) := by
          exact sub_eq_add_neg (-R + L + H * Complex.I) (H * Complex.I)
        _ = (-R + L) + (H * Complex.I + -(H * Complex.I)) := by
          exact add_assoc (-R + L) (H * Complex.I) (-(H * Complex.I))
        _ = (-R + L) + 0 := by
          exact congrArg (fun x : ℂ => (-R + L) + x) (add_neg_cancel (H * Complex.I))
        _ = -R + L := by
          exact add_zero (-R + L)
    calc
      L = R + (-R + L) := by
        calc
          L = 0 + L := by
            exact (zero_add L).symm
          _ = (R + -R) + L := by
            exact congrArg (fun x : ℂ => x + L) (add_right_neg R).symm
          _ = R + (-R + L) := by
            exact add_assoc R (-R) L
      _ = R + (C * Complex.I - H * Complex.I) := by
        exact congrArg (fun x : ℂ => R + x) hstep.symm
      _ = R + C * Complex.I - H * Complex.I := by
        exact (add_sub_assoc R (C * Complex.I) (H * Complex.I)).symm
  exact hsolve

/-- The scheduled tangent-boundary defect is the named left face plus the
isolated zero-pole horizontal remainder with the vertical tangent restored. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I_ownerZeroPoleAlgebra
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hleft :
      L =
        R + C * Complex.I - H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I_ownerZeroPoleAlgebra
      f F h u
  change R + C * Complex.I = L + H * Complex.I
  calc
    R + C * Complex.I = (R + C * Complex.I - H * Complex.I) + H * Complex.I := by
      calc
        R + C * Complex.I =
            (R + C * Complex.I) + 0 := by
          exact (add_zero (R + C * Complex.I)).symm
        _ =
            (R + C * Complex.I) + (-(H * Complex.I) + H * Complex.I) := by
          exact congrArg
            (fun x : ℂ => (R + C * Complex.I) + x)
            (neg_add_cancel (H * Complex.I)).symm
        _ =
            ((R + C * Complex.I) + -(H * Complex.I)) + H * Complex.I := by
          exact (add_assoc (R + C * Complex.I) (-(H * Complex.I)) (H * Complex.I)).symm
        _ =
            (R + C * Complex.I - H * Complex.I) + H * Complex.I := by
          exact congrArg
            (fun x : ℂ => x + H * Complex.I)
            (sub_eq_add_neg (R + C * Complex.I) (H * Complex.I)).symm
    _ = L + H * Complex.I := by
      exact congrArg (fun x : ℂ => x + H * Complex.I) hleft.symm

/-- Parameterized transport from tangent-boundary defect convergence and
horizontal decay to the scheduled left zero-pole face.  The horizontal theorem
is an input here so this file remains independent of the horizontal-estimate
owner layer. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect_and_horizontal_ownerZeroPoleAlgebra
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hdefect :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    hhorizontal.mul tendsto_const_nhds
  have hI_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      hI
  have hsub :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (0 - 0)) :=
    hdefect.sub hI_zero
  have hsub_zero :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u * Complex.I)
          atTop
          (𝓝 z))
      (sub_zero (0 : ℂ))
      hsub
  have hpointwise :
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u * Complex.I) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u) := by
    funext u
    let D : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u * Complex.I
    have hD : D = L + H :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I_ownerZeroPoleAlgebra
        f F h u
    change D - H = L
    calc
      D - H = (L + H) - H := by
        exact congrArg (fun x : ℂ => x - H) hD
      _ = (L + H) + -H := by
        exact sub_eq_add_neg (L + H) H
      _ = L + (H + -H) := by
        exact add_assoc L H (-H)
      _ = L + 0 := by
        exact congrArg (fun x : ℂ => L + x) (add_neg_cancel H)
      _ = L := by
        exact add_zero L
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise
    hsub_zero

/-- Parameterized standard-boundary residue transport to the scheduled left
zero-pole face.  The centered right-face limit is passed in explicitly, so this
lemma remains upstream of the right zero-pole Cauchy inversion theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_standardBoundaryResidue_and_orientationDefect_ownerZeroPoleAlgebra
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℂ)
    (hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 A))
    (hcancel : A + B * Complex.I = 0)
    (hstandard :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B)
    (horientation :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hstandardI_event :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I) =
       ᶠ[atTop]
        (fun _u : ℝ => B * Complex.I) := by
    exact hstandard.mono
      (fun u hu =>
        congrArg (fun z : ℂ => z * Complex.I) hu)
  have hstandardI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    hstandardI_event.tendsto_iff.2 tendsto_const_nhds
  have horientationI_raw :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    horientation.mul tendsto_const_nhds
  have horientationI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      horientationI_raw
  have htangentI :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I + 0)) := by
    have hsum :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 (B * Complex.I + 0)) :=
      hstandardI.add horientationI
    have hpoint :
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) := by
      funext u
      have htangent :
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) =
            zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
                f F (h.height_schedule.height u) :=
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
          f F h u
      calc
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
              f F (h.height_schedule.height u) * Complex.I =
            (zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
                f F (h.height_schedule.height u)) * Complex.I := by
          exact
            (add_mul
              (zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u))
              (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
                f F (h.height_schedule.height u))
              Complex.I).symm
        _ =
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I := by
          exact congrArg (fun z : ℂ => z * Complex.I) htangent.symm
    exact Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop (𝓝 (B * Complex.I + 0)))
      hpoint
      hsum
  have htangentI_value :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      (add_zero (B * Complex.I))
      htangentI
  have hdefect :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) * Complex.I)
        atTop
        (𝓝 0) := by
    have hsum :
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 (A + B * Complex.I)) :=
      hright.add htangentI_value
    exact Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
                f F (h.height_schedule.height u) * Complex.I)
          atTop
          (𝓝 z))
      hcancel
      hsum
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect_and_horizontal_ownerZeroPoleAlgebra
      f F h hdefect hhorizontal

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
