import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ScheduledBoundaryIdentities

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

/-- Positive-height finite Cauchy equality for the `s = 0` rectangle boundary
gives the scheduled limit at an arbitrary residue value. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (K : ℂ)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F T = K) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 K) := by
  have hevent :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u)) =
       ᶠ[atTop]
      (fun _u : ℝ => K) := by
    exact h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        hpositive (h.height_schedule.height u) hu)
  exact hevent.tendsto_iff.2 tendsto_const_nhds

/-- Positive-height finite Cauchy equality for the `s = 0` rectangle boundary gives
the scheduled centered boundary-residue limit. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_centeredPolePhi_of_positiveHeight_boundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hpositive :
      ∀ T : ℝ,
        0 < T →
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F T =
            1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral_tendsto_of_positiveHeight_boundaryResidue
      f F h (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)
      hpositive

/-- Algebraic transport from the finite `s = 0` rectangle boundary residue
limit to the right zero-pole vertical channel, for an arbitrary residue value.

This isolates the non-circular analytic inputs: the finite-rectangle boundary
residue, the left-face decay, and the horizontal-edge decay. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_rectangleBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (K : ℂ)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K)) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 K) := by
  have hleft_minus_horizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u)
        atTop
        (𝓝 (0 - 0)) :=
    hleft.sub hhorizontal
  have hboundaryK :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 K) :=
    hboundary
  have hsum :
      Tendsto
        (fun u : ℝ =>
          (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
              f F h u) +
            zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
              f F (h.height_schedule.height u))
        atTop
        (𝓝 ((0 - 0) + K)) :=
    hleft_minus_horizontal.add hboundaryK
  have hright_fun :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)) =
      (fun u : ℝ =>
        (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
        f F (h.height_schedule.height u)
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u
    let C : ℂ :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)
    have hC : C = R - L + H :=
      zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledRectangleBoundaryIntegral_eq_vertical_add_horizontal
        f F h u
    change R = (L - H) + C
    exact rightSide_eq_left_sub_horizontal_add_boundary_of_boundary_eq R L H C hC
  have htarget :
      (0 - 0 : ℂ) + K = K := by
    calc
      (0 - 0 : ℂ) + K = (0 + -0 : ℂ) + K := by
        exact congrArg (fun z : ℂ => z + K) (sub_eq_add_neg 0 0)
      _ = (0 : ℂ) + K := by
        exact congrArg (fun z : ℂ => (0 + z : ℂ) + K) (neg_zero : -(0 : ℂ) = 0)
      _ = K := by
        exact zero_add K
  exact Eq.subst
    (motive := fun φ : ℝ → ℂ =>
      Tendsto φ atTop (𝓝 K))
    hright_fun.symm
    (Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            (zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u) +
              zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
                f F (h.height_schedule.height u))
          atTop
          (𝓝 z))
      htarget
      hsum)

/-- Algebraic transport from the finite `s = 0` rectangle boundary residue limit
to the right zero-pole vertical channel.

This isolates the non-circular analytic inputs: the centered finite-rectangle
boundary residue, the left-face decay, and the horizontal-edge decay. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_centeredPolePhi_of_rectangleBoundaryResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hleft :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0))
    (hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u)
        atTop
        (𝓝 0))
    (hboundary :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_rectangleBoundaryResidue
      f F h (1 / (1 / 2 : ℂ) * zetaCompletedExplicitFormulaPhi f 0)
      hleft hhorizontal hboundary

/-- Right-face zero-pole vertical-inversion limit for the `s = 0`
correction pole, in its contour-side normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_value_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
  have hinversion :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion
            f F h u)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalInversionValue f)) := by
    exact
      zetaCompletedExplicitFormulaCorrectionRightZeroPoleScheduledVerticalInversion_tendsto_value
        f F h
  exact
    zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral_tendsto_of_scheduledVerticalInversion
      f F h hinversion

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
