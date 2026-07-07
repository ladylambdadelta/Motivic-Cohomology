import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleTangentDefectRate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleSquarePuncturedProjectBridge

/-!
# Quantitative zero-pole residue tail estimate

This file owns the direct inverse-quadratic residue-tail estimate for the
standard-to-tangent zero-pole boundary transport.  It is upstream of the
left off-pole Cauchy value: it proves only the local finite-residue tail,
not the left-face decay theorem itself.
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

/-- Quantitative tangent-boundary residue transport for the `s = 0` correction
pole.  The standard-boundary residue and the scheduled horizontal edge estimate
combine to give this tangent-boundary inverse-quadratic rate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eventual_inverseQuadratic_of_standardResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MB : ℝ,
      0 < MB ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) -
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))‖
            ≤ MB *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  let MH : ℝ := C * L + C * L
  let K : ℝ := (1 : ℝ) + (MH + MH)
  let MB : ℝ := |K| + 1
  have hMBpos : 0 < MB :=
    add_pos_of_nonneg_of_pos (abs_nonneg K) zero_lt_one
  have hstandard_event :
      ∀ᶠ u in atTop,
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B :=
    h.height_schedule.eventually_height_pos.mono
      (fun u hu =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F h (T := h.height_schedule.height u) hu)
  have hstandard :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ (1 : ℝ) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    hstandard_event.mono
      (fun u hu =>
        let S : ℂ :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u)
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hnorm : ‖S - B‖ = 0 := by
          calc
            ‖S - B‖ = ‖B - B‖ := by
              exact congrArg (fun z : ℂ => ‖z - B‖) hu
            _ = ‖(0 : ℂ)‖ := by
              exact congrArg norm (sub_self B)
            _ = 0 := norm_zero
        have hbase_nonneg :
            0 ≤ 1 + ‖(F.rectangle (h.height_schedule.height u)).T‖ :=
          add_nonneg zero_le_one (norm_nonneg _)
        have hq_nonneg : 0 ≤ q :=
          zpow_nonneg hbase_nonneg (-(2 : ℤ))
        have htarget_nonneg : 0 ≤ (1 : ℝ) * q :=
          mul_nonneg zero_le_one hq_nonneg
        Eq.subst
          (motive := fun x : ℝ => x ≤ (1 : ℝ) * q)
          hnorm.symm
          htarget_nonneg)
  have hhorizontal :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
          ≤ MH *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    exact
      show
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
            ≤ (C * L + C * L) *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) from
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_ownerZeroPoleHorizontal
          f F h
  have hraw :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ K *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    explicitFormula_tangentBoundary_eventual_inverseQuadratic_of_standard_and_horizontal
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
          f F h u)
      B (1 : ℝ) MH
      (fun u : ℝ => (F.rectangle (h.height_schedule.height u)).T)
      (fun u : ℝ => by
        let S : ℂ :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u)
        let T : ℂ :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u)
        let H : ℂ :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
            f F h u
        let D : ℂ :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleTangentOrientationDefect
            f F (h.height_schedule.height u)
        have htangent :
            T = S + D :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledTangentBoundary_eq_standard_add_orientationDefect
            f F h u
        have hdefect :
            D = H + H :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledOrientationDefect_eq_horizontal_add_horizontal
            f F h u
        show T = S + (H + H)
        exact
          Eq.trans htangent
          (congrArg
            (fun z : ℂ => S + z)
            hdefect))
      hstandard hhorizontal
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ MB *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    hraw.mono
      (fun u hu =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hbase_nonneg :
            0 ≤ 1 + ‖(F.rectangle (h.height_schedule.height u)).T‖ :=
          add_nonneg zero_le_one (norm_nonneg _)
        have hq_nonneg : 0 ≤ q :=
          zpow_nonneg hbase_nonneg (-(2 : ℤ))
        have hK_le_MB : K ≤ MB :=
          le_trans (le_abs_self K) (le_add_of_nonneg_right zero_le_one)
        have hmul : K * q ≤ MB * q :=
          mul_le_mul_of_nonneg_right hK_le_MB hq_nonneg
        le_trans hu hmul)
  exact ⟨MB, hMBpos, hbound⟩

/-- Limit form of the zero-pole tangent-boundary residue-tail estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidue_ownerResidueTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝
        ((2 * (Real.pi : ℂ) * Complex.I) *
          (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ))))) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (-(1 / 2 : ℂ)))
  match
    zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_eventual_inverseQuadratic_of_standardResidue
      f F h with
  | ⟨MB, _hMBpos, hbound⟩ =>
      have hmajorant :
          Tendsto
            (fun u : ℝ =>
              MB *
                (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^
                  (-(2 : ℤ)))
            atTop
            (𝓝 0) :=
        zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero_ownerShared
          F h.height_schedule MB
      exact
        tendsto_iff_norm_sub_tendsto_zero.2
          (squeeze_zero'
            (Eventually.of_forall
              (fun u : ℝ =>
                norm_nonneg
                  (zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral
                    f F (h.height_schedule.height u) - B)))
            hbound
            hmajorant)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
