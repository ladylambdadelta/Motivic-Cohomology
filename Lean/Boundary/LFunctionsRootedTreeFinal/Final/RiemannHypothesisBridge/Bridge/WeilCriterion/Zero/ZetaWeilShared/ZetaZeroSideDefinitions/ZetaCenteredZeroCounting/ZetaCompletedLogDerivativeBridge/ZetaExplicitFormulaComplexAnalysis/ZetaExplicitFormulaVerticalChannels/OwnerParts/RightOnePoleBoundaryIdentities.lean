import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleOscillatoryIntegral

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

/-- Lower-owner scheduled `s = 1` boundary identity used by the right one-pole
oscillatory estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal_ownerRightOnePoleBoundary
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
      exact Eq.refl _
    _ = (R - L + U) + -B := by
      exact sub_eq_add_neg (R - L + U) B
    _ = R - L + (U + -B) := by
      exact add_assoc (R - L) U (-B)
    _ = R - L + (U - B) := by
      exact congrArg (fun x : ℂ => R - L + x) (sub_eq_add_neg U B).symm
    _ = R - L + H := by
      exact Eq.refl _
/-- Solve the lower-owner scheduled `s = 1` rectangle identity for the right
vertical face. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary_ownerRightOnePoleBoundary
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
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal_ownerRightOnePoleBoundary
      f F h u
  change R = L - H + C
  exact rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq R L H C hC

/-- Lower-owner scheduled tangent `s = 1` boundary identity used by the right
one-pole oscillatory estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal_ownerRightOnePoleBoundary
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
    exact Eq.refl _
  calc
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T := by
      exact Eq.refl _
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

/-- Lower-owner pointwise orientation identity comparing the scheduled tangent
boundary with the standard rectangle-Cauchy boundary.  The discrepancy is
exactly two copies of the scheduled horizontal orientation remainder. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_standard_add_twice_horizontal_ownerRightOnePoleBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) =
      zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) +
        (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u) := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let U : ℂ :=
    zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let D : ℂ :=
    zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral
      f F (h.height_schedule.height u)
  let S : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hU :
      U =
        zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) := by
    exact zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_horizontal
      f F (h.height_schedule.height u)
  have hD :
      D =
        zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
          f F (h.height_schedule.height u) := by
    exact zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_horizontal
      f F (h.height_schedule.height u)
  have hH : H = U - D := by
    calc
      H =
          zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral
              f F (h.height_schedule.height u) := by
        exact zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eq
          f F h u
      _ = U - D := by
        exact congrArg₂ HSub.hSub hU.symm hD.symm
  have hS : S = D - U + R - L := by
    let U' : ℂ :=
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x)
    let D' : ℂ :=
      ∫ x in Set.Icc (1 - F.c) F.c,
        zetaCompletedExplicitFormulaCorrectionOnePoleKernel f
          (zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x)
    have hU_Icc : U = U' := by
      exact zetaCompletedExplicitFormulaCorrectionTopOnePoleTangentIntegral_eq_Icc
        f F (h.height_schedule.height u)
    have hD_Icc : D = D' := by
      exact zetaCompletedExplicitFormulaCorrectionBottomOnePoleTangentIntegral_eq_Icc
        f F (h.height_schedule.height u)
    calc
      S = D' - U' + R - L := by
        exact zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq
          f F (h.height_schedule.height u)
      _ = D - U' + R - L := by
        exact congrArg
          (fun x : ℂ => x - U' + R - L)
          hD_Icc.symm
      _ = D - U + R - L := by
        exact congrArg
          (fun x : ℂ => D - x + R - L)
          hU_Icc.symm
  let A : ℂ := R - L
  have htangent_AH : R - L + U - D = A + H := by
    calc
      R - L + U - D = (R - L) + (U - D) := by
        exact add_sub_assoc (R - L) U D
      _ = A + (U - D) := by
        exact Eq.refl _
      _ = A + H := by
        exact congrArg (fun z : ℂ => A + z) hH.symm
  have hstandard_AH : S = A - H := by
    calc
      S = D - U + R - L := hS
      _ = R - L - (U - D) := by
        exact
          explicitFormula_standardBoundary_horizontal_algebra
            R L U D
      _ = A - (U - D) := by
        exact Eq.refl _
      _ = A - H := by
        exact congrArg (fun z : ℂ => A - z) hH.symm
  change R - L + U - D = S + (H + H)
  calc
    R - L + U - D = A + H := htangent_AH
    _ = (A - H) + (H + H) := by
      exact
        explicitFormula_orientationDefect_horizontal_add_algebra A H
    _ = S + (H + H) := by
      exact congrArg
        (fun z : ℂ => z + (H + H))
        hstandard_AH.symm

/-- Solve the lower-owner tangent-contour boundary identity for the scheduled
right `s = 1` vertical face. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I_ownerRightOnePoleBoundary
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
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal_ownerRightOnePoleBoundary
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
  have hneg_I_mul_I : -(Complex.I * Complex.I) = (1 : ℂ) := by
    calc
      -(Complex.I * Complex.I) = -(-(1 : ℂ)) := by
        exact congrArg Neg.neg hI_mul_I
      _ = (1 : ℂ) := by
        exact neg_neg (1 : ℂ)
  have hI_mul_negI : Complex.I * (-Complex.I) = (1 : ℂ) := by
    calc
      Complex.I * (-Complex.I) = -(Complex.I * Complex.I) := by
        exact mul_neg Complex.I Complex.I
      _ = (1 : ℂ) := by
        exact hneg_I_mul_I
  have hC_mul_negI :
      C * (-Complex.I) = R - L + H * (-Complex.I) := by
    calc
      C * (-Complex.I) = (R * Complex.I - L * Complex.I + H) * (-Complex.I) := by
        exact congrArg (fun x : ℂ => x * (-Complex.I)) hC
      _ = ((R * Complex.I - L * Complex.I) + H) * (-Complex.I) := by
        exact Eq.refl _
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
          hneg_I_mul_I
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
          hI_mul_negI
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
        exact (add_sub_cancel L R).symm
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

/-- Norm form of the corrected tangent-boundary identity for the scheduled right
`s = 1` face.  The analytic residue theorem must bound the tangent defect
`left - tangentBoundary * I`; the horizontal remainder is separate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖ +
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    exact Eq.refl _
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - C * Complex.I + H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I_ownerRightOnePoleBoundary
      f F h u
  have hR : R = (L - C * Complex.I) + H * Complex.I :=
    Eq.trans hR_eq_vertical hvertical
  have hnorm :
      ‖(L - C * Complex.I) + H * Complex.I‖ ≤
        ‖L - C * Complex.I‖ + ‖H * Complex.I‖ :=
    norm_add_le (L - C * Complex.I) (H * Complex.I)
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
      ‖L - C * Complex.I‖ + ‖H * Complex.I‖ =
        ‖L - C * Complex.I‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L - C * Complex.I‖ + x) hH_norm
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ ‖L - C * Complex.I‖ + ‖H‖)
    hR.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        ‖(L - C * Complex.I) + H * Complex.I‖ ≤ x)
      htarget
      hnorm)

/-- Projection-subtracted norm form of the corrected tangent-boundary identity
for the scheduled right `s = 1` face. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_sub_projection_norm_le_tangentBoundaryProjectionDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) (P : ℂ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u - P‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I - P‖ +
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    exact Eq.refl _
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - C * Complex.I + H * Complex.I :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I_ownerRightOnePoleBoundary
      f F h u
  have hR : R = (L - C * Complex.I) + H * Complex.I :=
    Eq.trans hR_eq_vertical hvertical
  have hsub :
      R - P = (L - C * Complex.I - P) + H * Complex.I := by
    calc
      R - P = ((L - C * Complex.I) + H * Complex.I) - P := by
        exact congrArg (fun z : ℂ => z - P) hR
      _ = ((L - C * Complex.I) + H * Complex.I) + -P := by
        exact sub_eq_add_neg ((L - C * Complex.I) + H * Complex.I) P
      _ = (L - C * Complex.I + -P) + H * Complex.I := by
        calc
          ((L - C * Complex.I) + H * Complex.I) + -P =
              (L - C * Complex.I) + (H * Complex.I + -P) := by
            exact add_assoc (L - C * Complex.I) (H * Complex.I) (-P)
          _ = (L - C * Complex.I) + (-P + H * Complex.I) := by
            exact congrArg
              (fun z : ℂ => (L - C * Complex.I) + z)
              (add_comm (H * Complex.I) (-P))
          _ = ((L - C * Complex.I) + -P) + H * Complex.I := by
            exact (add_assoc (L - C * Complex.I) (-P) (H * Complex.I)).symm
      _ = (L - C * Complex.I - P) + H * Complex.I := by
        exact congrArg
          (fun z : ℂ => z + H * Complex.I)
          (sub_eq_add_neg (L - C * Complex.I) P).symm
  have hnorm :
      ‖(L - C * Complex.I - P) + H * Complex.I‖ ≤
        ‖L - C * Complex.I - P‖ + ‖H * Complex.I‖ :=
    norm_add_le (L - C * Complex.I - P) (H * Complex.I)
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
      ‖L - C * Complex.I - P‖ + ‖H * Complex.I‖ =
        ‖L - C * Complex.I - P‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L - C * Complex.I - P‖ + x) hH_norm
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤ ‖L - C * Complex.I - P‖ + ‖H‖)
      hsub.symm
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖(L - C * Complex.I - P) + H * Complex.I‖ ≤ x)
        htarget
        hnorm)

/-- Norm form of the finite-rectangle `s = 1` correction identity for the scheduled
right face.  This is the exact Cauchy bookkeeping output: the right off-pole face is
controlled by the opposite one-pole face, the one-pole horizontal remainder, and the
single-pole boundary integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_left_horizontal_boundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖ +
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    exact Eq.refl _
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - H + C :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary_ownerRightOnePoleBoundary
      f F h u
  have hR : R = L - H + C :=
    Eq.trans hR_eq_vertical hvertical
  have hnorm_add :
      ‖L - H + C‖ ≤ ‖L - H‖ + ‖C‖ :=
    norm_add_le (L - H) C
  have hnorm_sub :
      ‖L - H‖ ≤ ‖L‖ + ‖H‖ :=
    norm_sub_le L H
  have hsum_left :
      ‖L - H‖ + ‖C‖ ≤ (‖L‖ + ‖H‖) + ‖C‖ :=
    add_le_add_right hnorm_sub ‖C‖
  have hsum :
      ‖L - H + C‖ ≤ (‖L‖ + ‖H‖) + ‖C‖ :=
    le_trans hnorm_add hsum_left
  have htarget_assoc :
      (‖L‖ + ‖H‖) + ‖C‖ = ‖L‖ + ‖H‖ + ‖C‖ := by
    exact Eq.refl _
  have hR_norm :
      ‖R‖ = ‖L - H + C‖ :=
    congrArg norm hR
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ ‖L‖ + ‖H‖ + ‖C‖)
    hR_norm.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖L - H + C‖ ≤ x)
      htarget_assoc
      hsum)

/-- Sharp norm form of the finite-rectangle `s = 1` correction cancellation identity.
The residue cancellation to be proved analytically is exactly the combined defect
`left-face + boundary`; the horizontal term is kept separate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ) :
    ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖ +
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u‖ := by
  let R : ℂ :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
      f F h u
  let L : ℂ :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
      f F (h.height_schedule.height u)
  let H : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
      f F h u
  let C : ℂ :=
    zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
      f F (h.height_schedule.height u)
  have hR_eq_vertical :
      R =
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) := by
    exact Eq.refl _
  have hvertical :
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u) =
        L - H + C :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_horizontal_add_boundary_ownerRightOnePoleBoundary
      f F h u
  have hR : R = L - H + C :=
    Eq.trans hR_eq_vertical hvertical
  have hrepack : L - H + C = (L + C) + -H := by
    calc
      L - H + C = (L + -H) + C := by
        exact congrArg (fun x : ℂ => x + C) (sub_eq_add_neg L H)
      _ = L + (-H + C) := by
        exact add_assoc L (-H) C
      _ = L + (C + -H) := by
        exact congrArg (fun x : ℂ => L + x) (add_comm (-H) C)
      _ = (L + C) + -H := by
        exact (add_assoc L C (-H)).symm
  have hR_repack : R = (L + C) + -H :=
    Eq.trans hR hrepack
  have hnorm :
      ‖(L + C) + -H‖ ≤ ‖L + C‖ + ‖-H‖ :=
    norm_add_le (L + C) (-H)
  have hneg_norm : ‖-H‖ = ‖H‖ :=
    norm_neg H
  have htarget :
      ‖L + C‖ + ‖-H‖ = ‖L + C‖ + ‖H‖ :=
    congrArg (fun x : ℝ => ‖L + C‖ + x) hneg_norm
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ ‖L + C‖ + ‖H‖)
    hR_repack.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖(L + C) + -H‖ ≤ x)
      htarget
      hnorm)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
