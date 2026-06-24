import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleBoundaryDefect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay

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

/-- Algebraic assembly of the two true left-zero analytic estimates.

The inputs are exactly the two upstream estimates exposed by the Cauchy
rectangle identity: the residue/boundary defect and the isolated `s = 0`
horizontal remainder.  This lemma contains no analytic shortcut; it only
transports those two bounds through the already proved boundary decomposition. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hboundary :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
            f F (h.height_schedule.height u)‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
            B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) -
      zetaCompletedExplicitFormulaCorrectionZeroPoleRectangleBoundaryIntegral
        f F (h.height_schedule.height u)‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  have hdecomp :
      ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖ ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_boundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    hboundary u
  have hH : H ≤ S + B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + (S + B * q) :=
    add_le_add hD hH
  have hrotate :
      A * q + (S + B * q) = S + (A * q + B * q) := by
    calc
      A * q + (S + B * q) = (A * q + S) + B * q := by
        exact (add_assoc (A * q) S (B * q)).symm
      _ = (S + A * q) + B * q := by
        exact congrArg (fun x : ℝ => x + B * q) (add_comm (A * q) S)
      _ = S + (A * q + B * q) := by
        exact add_assoc S (A * q) (B * q)
  have hfactor :
      A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htarget :
      A * q + (S + B * q) = S + (A + B) * q :=
    Eq.trans hrotate (congrArg (fun x : ℝ => S + x) hfactor)
  exact le_trans hdecomp (le_trans hsum (le_of_eq htarget))

/-- Adding a nonnegative explicit horizontal side term preserves an isolated
zero-pole horizontal inverse-quadratic estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hhorizontal :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
        f F h u‖
        ≤ ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let S : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hH : H ≤ B * q :=
    hhorizontal u
  have hnonneg : 0 ≤ S :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : B * q ≤ S + B * q := by
    calc
      B * q = 0 + B * q := by
        exact (zero_add (B * q)).symm
      _ ≤ S + B * q := by
        exact add_le_add_right hnonneg (B * q)
  exact le_trans hH hadd

/-- Exact sink for the left-zero scheduled rectangle cancellation from the
genuine tangent-contour Cauchy defect. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (htangent :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
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
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  refine ⟨A + B, add_pos hApos hBpos, ?_⟩
  intro u
  let q : ℝ :=
    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  let E : ℝ :=
    ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
  let L : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
      f F h u‖
  let D : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
        f F (h.height_schedule.height u) +
      zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u) * Complex.I‖
  let H : ℝ :=
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
      f F h u‖
  have hdecomp : L ≤ D + H :=
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
      f F h u
  have hD : D ≤ A * q :=
    htangent u
  have hH : H ≤ B * q :=
    hhorizontal u
  have hsum : D + H ≤ A * q + B * q :=
    add_le_add hD hH
  have hfactor : A * q + B * q = (A + B) * q :=
    (add_mul A B q).symm
  have htail : L ≤ (A + B) * q :=
    le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
  have hEnonneg : 0 ≤ E :=
    norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
  have hadd : (A + B) * q ≤ E + (A + B) * q := by
    calc
      (A + B) * q = 0 + (A + B) * q := by
        exact (zero_add ((A + B) * q)).symm
      _ ≤ E + (A + B) * q := by
        exact add_le_add_right hEnonneg ((A + B) * q)
  exact le_trans htail hadd

/-- Eventual version of the left-zero tangent Cauchy assembly.

This is the exact shape supplied by the current horizontal decay API: eventual
inverse-quadratic control of the tangent Cauchy defect and of the isolated
zero-pole horizontal term gives eventual inverse-quadratic control of the
scheduled left-zero oscillatory integral, up to the explicit horizontal side
term. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_eventually_scheduledRectangleCauchyCancellation_of_tangentCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
        f F h u‖
      ≤
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
          (A + B) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact (htangent.and hhorizontal).mono
    (fun u hpair =>
      let q : ℝ :=
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
      let E : ℝ :=
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
      let L : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
      let D : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionRightZeroPoleVerticalIntegral
            f F (h.height_schedule.height u) +
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
      let H : ℝ :=
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u‖
      have hdecomp : L ≤ D + H :=
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral_norm_le_tangentBoundaryDefect_add_horizontal
          f F h u
      have hD : D ≤ A * q :=
        hpair.1
      have hH : H ≤ B * q :=
        hpair.2
      have hsum : D + H ≤ A * q + B * q :=
        add_le_add hD hH
      have hfactor : A * q + B * q = (A + B) * q :=
        (add_mul A B q).symm
      have htail : L ≤ (A + B) * q :=
        le_trans hdecomp (le_trans hsum (le_of_eq hfactor))
      have hEnonneg : 0 ≤ E :=
        norm_nonneg (explicitFormulaScheduledHorizontalSideDifference f F h u)
      have hadd : (A + B) * q ≤ E + (A + B) * q := by
        calc
          (A + B) * q = 0 + (A + B) * q := by
            exact (zero_add ((A + B) * q)).symm
          _ ≤ E + (A + B) * q := by
            exact add_le_add_right hEnonneg ((A + B) * q)
      le_trans htail hadd)

/-- Exact sink for the left-zero scheduled rectangle cancellation.

The remaining analytic input is the all-height Cauchy estimate for the left
off-pole `s = 0` face.  Once that owner theorem is available, the already
proved boundary-defect identity and isolated horizontal estimate discharge the
scheduled rectangle cancellation statement. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_leftCauchy_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A B : ℝ)
    (hApos : 0 < A)
    (hBpos : 0 < B)
    (hleft :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u)‖
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
        ‖zetaCompletedExplicitFormulaCorrectionLeftZeroPoleScheduledOscillatoryIntegral
          f F h u‖
          ≤
            ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ +
              C *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionZeroPoleBoundaryDefect_inverseQuadratic_of_left_horizontal
      f F h A B hApos hBpos hleft hhorizontal with
  | ⟨D, hDpos, hD⟩ =>
      exact
        zetaCompletedExplicitFormulaCorrectionLeftZeroPole_scheduledRectangleCauchyCancellation_of_boundaryDefect_horizontal
          f F h D B hDpos hBpos hD
          (zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_explicit_add_of_inverseQuadratic
            f F h B hhorizontal)

/-- Left-face off-pole Cauchy limit for the `s = 0` pole contribution.

This is a genuine analytic decay theorem for the left face, which does not
contain the `s = 0` pole.  It must be proved from an off-pole contour/tail
estimate, not by cancelling against a centered right-zero value. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerChannelTransportAnalytic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLeftOffPoleDecay
      f F h

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
