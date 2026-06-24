import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.HorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleResidueTransport
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleTangentDefectRate

/-!
# Right one-pole off-pole decay estimate

This file owns the direct analytic decay input for the right `s = 1` off-pole
correction face.  The remaining analytic leaf is the eventual
inverse-quadratic off-pole bound; the limit theorem is a thin wrapper over the
existing squeeze theorem in `HorizontalEdgeBounds`.
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

/-- Quantitative tangent-defect control from independent right-face and
horizontal inverse-quadratic estimates.

This lemma is deliberately one-way: it does not use the tangent-defect estimate
to prove the right off-pole estimate, so it can be reused without creating the
cycle that the owner leaf must avoid. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentDefect_eventual_inverseQuadraticBound_of_rightOffPole_and_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (MR MH : ℝ)
    (hright :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ MR *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖
          ≤ MH *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) -
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u) * Complex.I‖
        ≤ (MR + MH) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    (hright.and hhorizontal).mono
      (fun u hu =>
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
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hR : R = L - C * Complex.I + H * Complex.I :=
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I
            f F h u
        have hdefect_eq : L - C * Complex.I = R - H * Complex.I := by
          calc
            L - C * Complex.I =
                (L - C * Complex.I + H * Complex.I) - H * Complex.I := by
              exact (add_sub_cancel (L - C * Complex.I) (H * Complex.I)).symm
            _ = R - H * Complex.I := by
              exact congrArg (fun z : ℂ => z - H * Complex.I) hR.symm
        have hnorm_split :
            ‖L - C * Complex.I‖ ≤ ‖R‖ + ‖H * Complex.I‖ := by
          exact
            Eq.subst
              (motive := fun z : ℂ => ‖z‖ ≤ ‖R‖ + ‖H * Complex.I‖)
              hdefect_eq.symm
              (norm_sub_le R (H * Complex.I))
        have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
          Complex.norm_I
        have hH_mul_norm : ‖H * Complex.I‖ = ‖H‖ := by
          calc
            ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := norm_mul H Complex.I
            _ = ‖H‖ * 1 := by
              exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
            _ = ‖H‖ := mul_one ‖H‖
        have hsum :
            ‖R‖ + ‖H * Complex.I‖ ≤ MR * q + MH * q := by
          have hH_bound : ‖H * Complex.I‖ ≤ MH * q :=
            Eq.subst
              (motive := fun x : ℝ => x ≤ MH * q)
              hH_mul_norm.symm
              hu.2
          exact add_le_add hu.1 hH_bound
        have hfactor :
            MR * q + MH * q = (MR + MH) * q :=
          (add_mul MR MH q).symm
        hnorm_split.trans (hsum.trans_eq hfactor))

/-- The scheduled right `s = 1` off-pole bound follows from the genuine
tangent-boundary defect estimate and the scheduled horizontal zero-excision
package.  This is the acyclic owner form used by the contour-cancellation
assembly. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_eventual_inverseQuadraticBound_of_tangentDefect
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (A : ℝ)
    (hApos : 0 < A)
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I‖
          ≤ A *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∃ M : ℝ,
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
      h with
  | ⟨E, hTopMem, hBottomMem⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_offPoleTailBound_ownerGap
          f F h A hApos htangent E hTopMem hBottomMem with
      | ⟨M, _hMpos, hMbound⟩ =>
          exact ⟨M, hMbound⟩

/-- Eventual inverse-quadratic off-pole bound for the scheduled right `s = 1`
correction face. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_eventual_inverseQuadraticBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ M : ℝ,
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eventual_inverseQuadratic_of_standardResidue
      f F h with
  | ⟨ML, hMLpos, hleft⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eventual_inverseQuadratic_of_standardResidue
          f F h with
      | ⟨MB, hMBpos, htangent⟩ =>
          let B : ℂ :=
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))
          have hcancel : B * Complex.I - B * Complex.I = 0 :=
            sub_self (B * Complex.I)
          have hdefect :
              ∀ᶠ u in atTop,
                ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
                    f F (h.height_schedule.height u) -
                  zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
                    f F (h.height_schedule.height u) * Complex.I‖
                  ≤ (ML + MB) *
                    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
            zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_eventual_inverseQuadratic_of_component_rates
              f F h (B * Complex.I) B ML MB hcancel hleft htangent
          exact
            zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_eventual_inverseQuadraticBound_of_tangentDefect
              f F h (ML + MB) (add_pos hMLpos hMBpos) hdefect

/-- Direct off-pole Cauchy decay for the scheduled right `s = 1` correction
face, obtained from the eventual inverse-quadratic bound. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_eventual_inverseQuadraticBound
      f F h with
  | ⟨M, hM⟩ =>
      exact
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_eventualOffPoleTailBound
          f F h M hM

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
