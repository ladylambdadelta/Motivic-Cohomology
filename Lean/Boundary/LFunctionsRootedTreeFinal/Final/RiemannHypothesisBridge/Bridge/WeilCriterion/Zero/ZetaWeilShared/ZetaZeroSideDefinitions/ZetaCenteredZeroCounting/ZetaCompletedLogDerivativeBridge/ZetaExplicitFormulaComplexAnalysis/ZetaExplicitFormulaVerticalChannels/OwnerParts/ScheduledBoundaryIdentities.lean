import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledHorizontalDifferences

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

/-- The scheduled left-face off-pole `s = 0` correction integral, isolated as
the object controlled by the contour-cancellation argument. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) : ℂ :=
  ∫ t in
      Set.Icc
        (-(F.rectangle (h.height_schedule.height u)).T)
        (F.rectangle (h.height_schedule.height u)).T,
      (-1 /
          zetaCompletedExplicitFormulaLeftPath
            (F.rectangle (h.height_schedule.height u)) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)

/-- Definition transport from the explicit left-face off-pole correction
integral to its scheduled owner name. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledOscillatoryIntegral_eq_named
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    (∫ t in
        Set.Icc
          (-(F.rectangle (h.height_schedule.height u)).T)
          (F.rectangle (h.height_schedule.height u)).T,
        (-1 /
            zetaCompletedExplicitFormulaLeftPath
              (F.rectangle (h.height_schedule.height u)) t) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaLeftPath
                (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- The scheduled left zero-pole oscillatory integral is the left zero-pole
vertical integral evaluated at the scheduled height. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_eq_scheduledOscillatoryIntegral
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u :=
  rfl

/-- The scheduled `s = 0` boundary integral is the right side minus the left side plus
the scheduled `s = 0` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u
  change C = R - L + H
  calc
    C = R - L + U - B := by
      rfl
    _ = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = R - L + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = R - L + (U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (sub_eq_add_neg U B).symm
    _ = R - L + H := by
      rfl

/-- The scheduled genuine `s = 0` contour boundary is the vertical-tangent
difference plus the scheduled horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u
  have htangent :
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T =
        R * Complex.I - L * Complex.I + U - B :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hH : H = U - B := by
    rfl
  calc
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral f F T := by
      rfl
    _ = R * Complex.I - L * Complex.I + U - B := htangent
    _ = R * Complex.I - L * Complex.I + (U - B) := by
      calc
        R * Complex.I - L * Complex.I + U - B =
            (R * Complex.I - L * Complex.I + U) + -B := by
          exact sub_eq_add_neg (R * Complex.I - L * Complex.I + U) B
        _ = R * Complex.I - L * Complex.I + (U + -B) := by
          exact add_assoc (R * Complex.I - L * Complex.I) U (-B)
        _ = R * Complex.I - L * Complex.I + (U - B) := by
          exact congrArg
            (fun x : ℂ => R * Complex.I - L * Complex.I + x)
            (sub_eq_add_neg U B).symm
    _ = R * Complex.I - L * Complex.I + H := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x) hH.symm

/-- The scheduled `s = 1` boundary integral is the right side minus the left side plus
the scheduled `s = 1` horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  change C = R - L + H
  calc
    C = R - L + U - B := by
      rfl
    _ = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = R - L + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = R - L + (U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (sub_eq_add_neg U B).symm
    _ = R - L + H := by
      rfl

/-- The early right-face off-pole `s = 1` vertical integral isolated from the
single-pole rectangle boundary identity. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u +
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hC : C = R - L + H :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
      f F h u
  change R = L - H + C
  exact rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq R L H C hC

/-- The scheduled genuine `s = 1` contour boundary is the vertical-tangent
difference plus the scheduled horizontal remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I -
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u := by
  let T : ℝ := h.height_schedule.height u
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
  let B : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u
  have htangent :
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T =
        R * Complex.I - L * Complex.I + U - B :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F T
  have hH : H = U - B := by
    rfl
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T := by
      rfl
    _ = R * Complex.I - L * Complex.I + U - B := htangent
    _ = R * Complex.I - L * Complex.I + (U - B) := by
      calc
        R * Complex.I - L * Complex.I + U - B =
            (R * Complex.I - L * Complex.I + U) + -B := by
          exact sub_eq_add_neg (R * Complex.I - L * Complex.I + U) B
        _ = R * Complex.I - L * Complex.I + (U + -B) := by
          exact add_assoc (R * Complex.I - L * Complex.I) U (-B)
        _ = R * Complex.I - L * Complex.I + (U - B) := by
          exact congrArg
            (fun x : ℂ => R * Complex.I - L * Complex.I + x)
            (sub_eq_add_neg U B).symm
    _ = R * Complex.I - L * Complex.I + H := by
      exact congrArg (fun x : ℂ => R * Complex.I - L * Complex.I + x) hH.symm

/-- Solve the corrected tangent-contour boundary identity for the scheduled
right `s = 1` vertical face.  This is the non-circular replacement for the old
unweighted rectangle-boundary bookkeeping. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I +
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u * Complex.I := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hC : C = R * Complex.I - L * Complex.I + H :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal
      f F h u
  have hI_mul_I : Complex.I * Complex.I = -(1 : ℂ) :=
    Complex.I_mul_I
  have hnegI_mul_I : (-Complex.I) * Complex.I = (1 : ℂ) := by
    calc
      (-Complex.I) * Complex.I = -(Complex.I * Complex.I) := by
        exact neg_mul Complex.I Complex.I
      _ = -(-(1 : ℂ)) := by
        exact congrArg Neg.neg hI_mul_I
      _ = (1 : ℂ) := by
        exact neg_neg (1 : ℂ)
  have hC_mul_negI :
      C * (-Complex.I) = R - L + H * (-Complex.I) := by
    calc
      C * (-Complex.I) = (R * Complex.I - L * Complex.I + H) * (-Complex.I) := by
        exact congrArg (fun x : ℂ => x * (-Complex.I)) hC
      _ = ((R * Complex.I - L * Complex.I) + H) * (-Complex.I) := by
        rfl
      _ = (R * Complex.I - L * Complex.I) * (-Complex.I) + H * (-Complex.I) := by
        exact add_mul (R * Complex.I - L * Complex.I) H (-Complex.I)
      _ = ((R * Complex.I) + -(L * Complex.I)) * (-Complex.I) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x * (-Complex.I) + H * (-Complex.I))
          (sub_eq_add_neg (R * Complex.I) (L * Complex.I))
      _ =
          ((R * Complex.I) * (-Complex.I) + (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x + H * (-Complex.I))
          (add_mul (R * Complex.I) (-(L * Complex.I)) (-Complex.I))
      _ =
          (R * (Complex.I * (-Complex.I)) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_assoc R Complex.I (-Complex.I))
      _ =
          (R * (-(Complex.I * Complex.I)) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_neg Complex.I Complex.I)
      _ =
          (R * (1 : ℂ) +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R * x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          hnegI_mul_I
      _ =
          (R +
              (-(L * Complex.I)) * (-Complex.I)) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (x + (-(L * Complex.I)) * (-Complex.I)) + H * (-Complex.I))
          (mul_one R)
      _ =
          (R +
              -((L * Complex.I) * (-Complex.I))) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + x) + H * (-Complex.I))
          (neg_mul (L * Complex.I) (-Complex.I))
      _ =
          (R +
              -(L * (Complex.I * (-Complex.I)))) +
            H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -x) + H * (-Complex.I))
          (mul_assoc L Complex.I (-Complex.I))
      _ =
          (R + -(L * (1 : ℂ))) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -(L * x)) + H * (-Complex.I))
          hnegI_mul_I
      _ = (R + -L) + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => (R + -x) + H * (-Complex.I))
          (mul_one L)
      _ = R - L + H * (-Complex.I) := by
        exact congrArg
          (fun x : ℂ => x + H * (-Complex.I))
          (sub_eq_add_neg R L).symm
  have hsolve :
      R = L + C * (-Complex.I) - H * (-Complex.I) := by
    have hstep :
        C * (-Complex.I) - H * (-Complex.I) = R - L := by
      calc
        C * (-Complex.I) - H * (-Complex.I) =
            (R - L + H * (-Complex.I)) - H * (-Complex.I) := by
          exact congrArg (fun x : ℂ => x - H * (-Complex.I)) hC_mul_negI
        _ = ((R - L) + H * (-Complex.I)) + -(H * (-Complex.I)) := by
          exact sub_eq_add_neg (R - L + H * (-Complex.I)) (H * (-Complex.I))
        _ = (R - L) + (H * (-Complex.I) + -(H * (-Complex.I))) := by
          exact add_assoc (R - L) (H * (-Complex.I)) (-(H * (-Complex.I)))
        _ = (R - L) + 0 := by
          exact congrArg (fun x : ℂ => (R - L) + x) (add_neg_cancel (H * (-Complex.I)))
        _ = R - L := by
          exact add_zero (R - L)
    calc
      R = L + (R - L) := by
        exact (add_sub_cancel'_right L R).symm
      _ = L + (C * (-Complex.I) - H * (-Complex.I)) := by
        exact congrArg (fun x : ℂ => L + x) hstep.symm
      _ = L + C * (-Complex.I) - H * (-Complex.I) := by
        exact (add_sub_assoc L (C * (-Complex.I)) (H * (-Complex.I))).symm
  calc
    R = L + C * (-Complex.I) - H * (-Complex.I) := hsolve
    _ = L - C * Complex.I + H * Complex.I := by
      calc
        L + C * (-Complex.I) - H * (-Complex.I) =
            L + -(C * Complex.I) - H * (-Complex.I) := by
          exact congrArg
            (fun x : ℂ => L + x - H * (-Complex.I))
            (mul_neg C Complex.I)
        _ = L - C * Complex.I - H * (-Complex.I) := by
          exact congrArg
            (fun x : ℂ => x - H * (-Complex.I))
            (sub_eq_add_neg L (C * Complex.I)).symm
        _ = L - C * Complex.I - -(H * Complex.I) := by
          exact congrArg
            (fun x : ℂ => L - C * Complex.I - x)
            (mul_neg H Complex.I)
        _ = L - C * Complex.I + H * Complex.I := by
          exact sub_neg_eq_add (L - C * Complex.I) (H * Complex.I)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
