import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds

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
left `s = 0` vertical face.  The finite single-pole Cauchy input for this side
is the tangent-boundary defect `right + boundary * I`; the horizontal remainder
is separate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
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

/-- Norm form of the corrected tangent-boundary identity for the scheduled left
`s = 0` face. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
  let Ls : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  have hnamed :
      Ls =
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    rfl
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) =
        R + C * Complex.I - H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
      f F h u
  have hLs : Ls = (R + C * Complex.I) + -(H * Complex.I) := by
    calc
      Ls =
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) := hnamed
      _ = R + C * Complex.I - H * Complex.I := hvertical
      _ = (R + C * Complex.I) + -(H * Complex.I) := by
        exact sub_eq_add_neg (R + C * Complex.I) (H * Complex.I)
  have hnorm :
      ‖(R + C * Complex.I) + -(H * Complex.I)‖ ≤
        ‖R + C * Complex.I‖ + ‖-(H * Complex.I)‖ :=
    norm_add_le (R + C * Complex.I) (-(H * Complex.I))
  have hneg_norm : ‖-(H * Complex.I)‖ = ‖H * Complex.I‖ :=
    norm_neg (H * Complex.I)
  have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
    Complex.norm_I
  have hH_mul_I_norm : ‖H * Complex.I‖ = ‖H‖ := by
    calc
      ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
        exact norm_mul H Complex.I
      _ = ‖H‖ * 1 := by
        exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
      _ = ‖H‖ := by
        exact mul_one ‖H‖
  have htail_norm : ‖-(H * Complex.I)‖ = ‖H‖ :=
    Eq.trans hneg_norm hH_mul_I_norm
  have htarget :
      ‖R + C * Complex.I‖ + ‖-(H * Complex.I)‖ =
        ‖R + C * Complex.I‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖R + C * Complex.I‖ + x) htail_norm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ ‖R + C * Complex.I‖ + ‖H‖)
    hLs.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        ‖(R + C * Complex.I) + -(H * Complex.I)‖ ≤ x)
      htarget
      hnorm)

/-- The scheduled tangent-boundary defect is the named left face plus the isolated
zero-pole horizontal remainder with the vertical tangent restored. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
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
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_right_add_tangentBoundary_mul_I_sub_horizontal_mul_I
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

/-- The left scheduled zero-pole face converges to zero once the genuine tangent
Cauchy defect converges to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
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
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
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
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
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

/-- The genuine zero-pole tangent defect is bounded by the named left face and
the isolated horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_norm_le_left_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖ +
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖ := by
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
      f F h u
  have hD : D = L + H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
      f F h u
  have hnorm :
      ‖L + H * Complex.I‖ ≤ ‖L‖ + ‖H * Complex.I‖ :=
    norm_add_le L (H * Complex.I)
  have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
    Complex.norm_I
  have hH_norm : ‖H * Complex.I‖ = ‖H‖ := by
    calc
      ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
        exact norm_mul H Complex.I
      _ = ‖H‖ * 1 := by
        exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
      _ = ‖H‖ := by
        exact mul_one ‖H‖
  have htarget :
      ‖L‖ + ‖H * Complex.I‖ = ‖L‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L‖ + x) hH_norm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L‖ + ‖H‖)
    hD.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖L + H * Complex.I‖ ≤ x)
      htarget
      hnorm)

/-- Quantitative transport from a left-face inverse-quadratic estimate to the
genuine zero-pole tangent-defect inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_inverseQuadratic_of_left_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ C *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hD : D ≤ L + H :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_norm_le_left_add_horizontal
      f F h u
  have hL : L ≤ A * q :=
    hleft u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : L + H ≤ A * q + B * q :=
    add_le_add hL hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  exact le_trans hD (le_trans hsum (le_of_eq hfactor))

/-- The genuine zero-pole tangent defect tends to zero once the named left face
tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u)
        atTop
        (𝓝 0)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) := by
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
      f F h
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
  have hadd :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (0 + 0)) :=
    hleft.add hI_zero
  have hadd_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
              f F h u +
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_add 0)
      hadd
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
            f F h u +
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u * Complex.I) := by
    funext u
    exact
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_eq_left_add_horizontal_mul_I
        f F h u
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 0))
    hpointwise.symm
    hadd_zero

/-- The genuine zero-pole tangent defect has the same scheduled zero limit as
the named left face, since the isolated horizontal remainder vanishes. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_iff_leftZeroPole
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 0) ↔
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u)
      atTop
      (𝓝 0) :=
  Iff.intro
    (fun hdefect =>
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_tendsto_zero_of_tangentBoundaryDefect
        f F h hdefect)
    (fun hleft =>
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentBoundaryDefect_tendsto_zero_of_leftZeroPole
        f F h hleft)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
