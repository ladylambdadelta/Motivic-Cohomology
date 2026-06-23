import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.LeftZeroCancellation

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

/-- Algebraic transport from the finite `s = 1` rectangle boundary residue limit
to the left on-pole vertical channel.

The analytic input that remains upstream is the finite single-pole Cauchy
residue limit for `zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral`.
The right off-pole face and the horizontal one-pole remainder are already
controlled in this file. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_rectangleBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) := by
  let K : ℂ := 1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 + 0)) :=
    hright.add hhorizontal
  have hboundaryK :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K) :=
    hboundary
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((0 + 0) - K)) :=
    hsum.sub hboundaryK
  have hleft_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) := by
    funext u
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
    change L = R + H - C
    exact leftSide_eq_right_add_horizontal_sub_boundary_of_boundary_eq R L H C hC
  have htarget :
      (0 + 0 : ℂ) - K = -K := by
    calc
      (0 + 0 : ℂ) - K = 0 - K := by
        exact congrArg (fun z : ℂ => z - K) (zero_add (0 : ℂ))
      _ = 0 + -K := by
        exact sub_eq_add_neg 0 K
      _ = -K := by
        exact zero_add (-K)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 (-K)))
    hleft_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hdiff)

/-- Positive-height finite Cauchy equality for the `s = 1` rectangle boundary gives
the scheduled boundary residue limit. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F T =
            1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ =>
        1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  exact hevent.tendsto_iff.2 tendsto_const_nhds

/-- Positive-height finite `s = 1` rectangle Cauchy residue transport to the left
on-pole vertical channel. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral
            f F T =
            1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (-(1 / (1 - (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0))) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_neg_centeredPolePhi_of_rectangleBoundaryResidue
      f F h
      (zetaCompletedExplicitFormulaCorrectionOnePoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue
        f F h hpositive)

/-- Algebraic transport from the honest standard `s = 1` contour residue limit
to the left vertical side, with the standard rectangle orientation retained.

This is the value forced by the standard contour convention:
`standard = bottom - top + right * I - left * I`. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_standardBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (B : ℂ)
    (hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 B)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (B * Complex.I)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (B + 0)) :=
    hstandard.add hhorizontal
  have hsumB :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 B) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u)
          atTop
          (𝓝 z))
      (add_zero B)
      hsum
  have hsumI :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    hsumB.mul tendsto_const_nhds
  have hleft_expr :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) * Complex.I)
        atTop
        (𝓝 (0 + B * Complex.I)) :=
    hright.add hsumI
  have hleft_expr_target :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) +
            (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u) * Complex.I)
        atTop
        (𝓝 (B * Complex.I)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u) +
              (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
                  f F (h.height_schedule.height u) +
                zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                  f F h u) * Complex.I)
          atTop
          (𝓝 z))
      (zero_add (B * Complex.I))
      hleft_expr
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u) +
          (zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u) * Complex.I) := by
    funext u
    let T : ℝ := h.height_schedule.height u
    let R : ℂ := zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
    let L : ℂ := zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
    let H : ℂ := zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u
    let S : ℂ := zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral f F T
    let U : ℂ := zetaCompletedExplicitFormulaCorrectionTopOnePoleHorizontalIntegral f F T
    let D : ℂ := zetaCompletedExplicitFormulaCorrectionBottomOnePoleHorizontalIntegral f F T
    have hS : S = D - U + R * Complex.I - L * Complex.I := by
      have hRtan :
          zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T =
            R * Complex.I :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral_eq_vertical_mul_I
          f F T
      have hLtan :
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T =
            L * Complex.I :=
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral_eq_vertical_mul_I
          f F T
      calc
        S =
            D - U +
              zetaCompletedExplicitFormulaCorrectionRightOnePoleTangentIntegral f F T -
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
          rfl
        _ = D - U + R * Complex.I -
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T := by
          exact congrArg
            (fun z : ℂ =>
              D - U + z -
                zetaCompletedExplicitFormulaCorrectionLeftOnePoleTangentIntegral f F T)
            hRtan
        _ = D - U + R * Complex.I - L * Complex.I := by
          exact congrArg
            (fun z : ℂ => D - U + R * Complex.I - z)
            hLtan
    have hH : H = U - D := by
      rfl
    have hS_add_H : S + H = R * Complex.I - L * Complex.I := by
      have hDU_cancel : (D - U) + (U - D) = 0 := by
        calc
          (D - U) + (U - D) = (D - U) + -(D - U) := by
            exact congrArg (fun z : ℂ => (D - U) + z) (neg_sub D U).symm
          _ = 0 := by
            exact add_right_neg (D - U)
      calc
        S + H = (D - U + R * Complex.I - L * Complex.I) + H := by
          exact congrArg (fun z : ℂ => z + H) hS
        _ = (D - U + R * Complex.I - L * Complex.I) + (U - D) := by
          exact congrArg (fun z : ℂ => (D - U + R * Complex.I - L * Complex.I) + z) hH
        _ = R * Complex.I - L * Complex.I := by
          calc
            (D - U + R * Complex.I - L * Complex.I) + (U - D) =
                ((D - U) + R * Complex.I - L * Complex.I) + (U - D) := by
              rfl
            _ =
                ((D - U) + (R * Complex.I - L * Complex.I)) + (U - D) := by
              exact congrArg (fun z : ℂ => z + (U - D))
                (add_sub_assoc (D - U) (R * Complex.I) (L * Complex.I))
            _ =
                (R * Complex.I - L * Complex.I) + ((D - U) + (U - D)) := by
              calc
                ((D - U) + (R * Complex.I - L * Complex.I)) + (U - D) =
                    (D - U) + ((R * Complex.I - L * Complex.I) + (U - D)) := by
                  exact add_assoc (D - U) (R * Complex.I - L * Complex.I) (U - D)
                _ =
                    (D - U) + ((U - D) + (R * Complex.I - L * Complex.I)) := by
                  exact congrArg (fun z : ℂ => (D - U) + z)
                    (add_comm (R * Complex.I - L * Complex.I) (U - D))
                _ =
                    ((D - U) + (U - D)) + (R * Complex.I - L * Complex.I) := by
                  exact (add_assoc (D - U) (U - D) (R * Complex.I - L * Complex.I)).symm
                _ =
                    (R * Complex.I - L * Complex.I) + ((D - U) + (U - D)) := by
                  exact add_comm ((D - U) + (U - D)) (R * Complex.I - L * Complex.I)
            _ = (R * Complex.I - L * Complex.I) + 0 := by
              exact congrArg
                (fun z : ℂ => (R * Complex.I - L * Complex.I) + z)
                hDU_cancel
            _ = R * Complex.I - L * Complex.I := by
              exact add_zero (R * Complex.I - L * Complex.I)
    have hI_sq : Complex.I * Complex.I = -(1 : ℂ) :=
      Complex.I_mul_I
    have hsolve : L = R + (S + H) * Complex.I := by
      calc
        R + (S + H) * Complex.I =
            R + (R * Complex.I - L * Complex.I) * Complex.I := by
          exact congrArg (fun z : ℂ => R + z * Complex.I) hS_add_H
        _ = R + ((R * Complex.I) * Complex.I - (L * Complex.I) * Complex.I) := by
          exact congrArg (fun z : ℂ => R + z)
            (sub_mul (R * Complex.I) (L * Complex.I) Complex.I)
        _ = R + (R * (Complex.I * Complex.I) - L * (Complex.I * Complex.I)) := by
          exact congrArg
            (fun z : ℂ => R + z)
            (congrArg₂ HSub.hSub
              (mul_assoc R Complex.I Complex.I)
              (mul_assoc L Complex.I Complex.I))
        _ = R + (R * (-(1 : ℂ)) - L * (-(1 : ℂ))) := by
          exact congrArg
            (fun z : ℂ => R + (R * z - L * z))
            hI_sq
        _ = R + (-R - -L) := by
          exact congrArg
            (fun z : ℂ => R + z)
            (congrArg₂ HSub.hSub (mul_neg_one R) (mul_neg_one L))
        _ = R + (-R + L) := by
          exact congrArg (fun z : ℂ => R + z) (sub_neg_eq_add (-R) L)
        _ = (R + -R) + L := by
          exact (add_assoc R (-R) L).symm
        _ = 0 + L := by
          exact congrArg (fun z : ℂ => z + L) (add_right_neg R)
        _ = L := by
          exact zero_add L
    exact hsolve.symm
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ => Tendsto φ atTop (𝓝 (B * Complex.I)))
    hpointwise.symm
    hleft_expr_target

/-- Positive-height raw standard `s = 1` Cauchy transport to the left vertical
side, with the standard contour normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_positiveHeight_rawStandardCauchy
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F T =
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ =>
        (2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  have hstandard :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2)))) :=
    hevent.tendsto_iff.2 tendsto_const_nhds
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_standardBoundaryResidue
      f F h
      ((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2)))
      hstandard

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

/-- Left-face one-pole Cauchy limit for the `s = 1` correction pole, including the
left boundary orientation.

With the honest standard-contour normalization, the upstream finite Cauchy
input is the raw standard boundary theorem for
`zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral`.
The old centered `Phi f 0` target belongs to the later correction-channel
normalization and must not be supplied by this single-pole contour theorem.
-/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_of_positiveHeight_rawStandardCauchy
      f F h
      (fun T hT =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F h T hT)

/-- The right pole face transports to the pole at `s = 0`, evaluated at the centered
basepoint of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)) :=
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_ownerChannelTransportAnalytic
      f F h
  have hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 (((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) + 0)) :=
    Tendsto.add hzero hone
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaCorrectionRightPoleVerticalIntegral_eq_zero_add_one
      f h.phi_control F (h.height_schedule.height u)
  have htarget :
      ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0) + 0 =
        (1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0 :=
    add_zero ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 ((1 / (1 / 2 : ℂ)) * zetaCompletedExplicitFormulaPhi f 0)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- The left pole face transports with the standard-contour one-pole residue
normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) := by
  have hzero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
      f F h
  have hone :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)) :=
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_tendsto_standardContourResidue_ownerChannelTransportAnalytic
      f F h
  have hsum :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝
          (0 + (((2 * (Real.pi : ℂ) * Complex.I) *
            (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I))) :=
    Tendsto.add hzero hone
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) +
            zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u)) := by
    funext u
    exact zetaCompletedExplicitFormulaCorrectionLeftPoleVerticalIntegral_eq_zero_add_one
      f h.phi_control F (h.height_schedule.height u)
  have htarget :
      0 + (((2 * (Real.pi : ℂ) * Complex.I) *
        (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I) =
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I :=
    zero_add (((2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop
        (𝓝 (((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I)))
    hpointwise.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) +
              zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
