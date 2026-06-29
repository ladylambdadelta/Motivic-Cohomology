import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleTangentDefectRate
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleHorizontalEdgeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleBoundaryIdentities

/-!
# Quantitative one-pole residue tail estimate

This file owns the direct inverse-quadratic residue-tail estimate for the left
`s = 1` correction pole face.  Downstream Cauchy-cancellation files consume
this bound to prove off-pole decay, so this file must not import those
right-face cancellation consumers.

The proof cannot use the downstream right-face decay theorem whose proof
already consumes this left residue estimate.  The non-circular proof chain must
start at the residue-free right one-pole rectangle identity, then use the
finite one-pole Cauchy residue, horizontal inverse-quadratic bounds, and the
scheduled tangent-boundary normalization.  Horizontal estimates by themselves
do not imply the right vertical value.
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

/-- Compatibility bridge: inverse-quadratic decay for the off-pole right
`s = 1` correction face, independent of the left residue-tail theorem. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_direct_ownerResidueTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MR : ℝ,
      0 < MR ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u)‖
            ≤ MR *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral_eventual_inverseQuadratic_ownerOscillatory
      f F h with
  | ⟨MR, hMRpos, hMR⟩ =>
      exact
        ⟨MR, hMRpos,
          hMR.mono
            (fun u hu =>
              Eq.subst
                (motive := fun z : ℂ =>
                  ‖z‖ ≤
                    MR *
                      (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^
                        (-(2 : ℤ)))
                (show
                  zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
                    f F h u =
                  zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                    f F (h.height_schedule.height u) from
                  rfl)
                hu)⟩

/-- Quantitative tangent-boundary residue transport for the `s = 1` correction
pole.  The standard-boundary residue and the scheduled horizontal edge estimate
combine to give this tangent-boundary inverse-quadratic rate.

This theorem belongs upstream of right off-pole decay: it is a component of the
one-pole residue analysis, not a consequence of the off-pole cancellation
stack. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eventual_inverseQuadratic_of_standardResidue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ MB : ℝ,
      0 < MB ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
              f F (h.height_schedule.height u) -
            (2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))‖
            ≤ MB *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
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
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u) = B :=
    zetaCompletedExplicitFormulaCorrectionOnePole_eventually_standardBoundaryResidueValue_of_positiveHeight
      f F h B
      (fun T hT =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral_eq_rawCauchy_of_pos_height
          f F h T hT)
  have hstandard :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ (1 : ℝ) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    hstandard_event.mono
      (fun u hu =>
        let S : ℂ :=
          zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
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
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
          ≤ MH *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    change
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
    exact
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
        f F h
  have hraw :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ K *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    explicitFormula_tangentBoundary_eventual_inverseQuadratic_of_standard_and_horizontal
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleStandardRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
          f F (h.height_schedule.height u))
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u)
      B
      (1 : ℝ)
      MH
      (fun u : ℝ => (F.rectangle (h.height_schedule.height u)).T)
      (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_standard_add_twice_horizontal_ownerRightOnePoleBoundary
        f F h)
      hstandard
      hhorizontal
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
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
        have hK_le_abs : K ≤ |K| :=
          le_abs_self K
        have habs_le_MB : |K| ≤ MB :=
          le_add_of_nonneg_right zero_le_one
        have hK_le_MB : K ≤ MB :=
          le_trans hK_le_abs habs_le_MB
        have hscale : K * q ≤ MB * q :=
          mul_le_mul_of_nonneg_right hK_le_MB hq_nonneg
        le_trans hu hscale)
  exact ⟨MB, hMBpos, hbound⟩

/-- Non-circular rate assembly for the left `s = 1` residue face from the
direct right-face tail, tangent-boundary residue rate, and horizontal edge
rate. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eventual_inverseQuadratic_of_right_tangent_horizontal
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℂ) (MR MB MH : ℝ)
    (hright :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u)‖
          ≤ MR *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (htangent :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) - B‖
          ≤ MB *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hhorizontal :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u‖
          ≤ MH *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
          f F (h.height_schedule.height u) - B * Complex.I‖
        ≤ (MR + (MB + MH)) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact (hright.and (htangent.and hhorizontal)).mono
    (fun u hu =>
      let T : ℝ := h.height_schedule.height u
      let R : ℂ :=
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral f F T
      let L : ℂ :=
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral f F T
      let C : ℂ :=
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral f F T
      let H : ℂ :=
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
          f F h u
      let q : ℝ := (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))
      have hC :
          C = R * Complex.I - L * Complex.I + H :=
        zetaCompletedExplicitFormulaCorrectionOnePoleScheduledTangentRectangleBoundaryIntegral_eq_verticalTangent_add_horizontal_ownerRightOnePoleBoundary
          f F h u
      have hleft_error :
          L - B * Complex.I =
            R + (C - B) * Complex.I - H * Complex.I :=
        explicitFormula_leftResidueError_eq_right_add_tangentError_mul_I_sub_horizontal_mul_I
          R L C H B hC
      have hsplit :
          ‖R + (C - B) * Complex.I - H * Complex.I‖
            ≤ (‖R‖ + ‖(C - B) * Complex.I‖) + ‖H * Complex.I‖ := by
        have hsub :
            ‖R + (C - B) * Complex.I - H * Complex.I‖
              ≤ ‖R + (C - B) * Complex.I‖ + ‖H * Complex.I‖ :=
          norm_sub_le (R + (C - B) * Complex.I) (H * Complex.I)
        have hadd :
            ‖R + (C - B) * Complex.I‖
              ≤ ‖R‖ + ‖(C - B) * Complex.I‖ :=
          norm_add_le R ((C - B) * Complex.I)
        exact le_trans hsub (add_le_add_right hadd ‖H * Complex.I‖)
      have hI_norm : ‖Complex.I‖ = (1 : ℝ) :=
        Complex.norm_I
      have htangent_mul_norm :
          ‖(C - B) * Complex.I‖ = ‖C - B‖ := by
        calc
          ‖(C - B) * Complex.I‖ = ‖C - B‖ * ‖Complex.I‖ := by
            exact norm_mul (C - B) Complex.I
          _ = ‖C - B‖ * 1 := by
            exact congrArg (fun x : ℝ => ‖C - B‖ * x) hI_norm
          _ = ‖C - B‖ := by
            exact mul_one ‖C - B‖
      have hhorizontal_mul_norm :
          ‖H * Complex.I‖ = ‖H‖ := by
        calc
          ‖H * Complex.I‖ = ‖H‖ * ‖Complex.I‖ := by
            exact norm_mul H Complex.I
          _ = ‖H‖ * 1 := by
            exact congrArg (fun x : ℝ => ‖H‖ * x) hI_norm
          _ = ‖H‖ := by
            exact mul_one ‖H‖
      have hcomponent :
          (‖R‖ + ‖(C - B) * Complex.I‖) + ‖H * Complex.I‖
            ≤ (MR * q + MB * q) + MH * q := by
        have htangent_bound :
            ‖(C - B) * Complex.I‖ ≤ MB * q :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ MB * q)
            htangent_mul_norm.symm
            hu.2.1
        have hhorizontal_bound :
            ‖H * Complex.I‖ ≤ MH * q :=
          Eq.subst
            (motive := fun x : ℝ => x ≤ MH * q)
            hhorizontal_mul_norm.symm
            hu.2.2
        exact add_le_add (add_le_add hu.1 htangent_bound) hhorizontal_bound
      have hfactor :
          (MR * q + MB * q) + MH * q =
            (MR + (MB + MH)) * q := by
        calc
          (MR * q + MB * q) + MH * q =
              (MR + MB) * q + MH * q := by
            exact congrArg (fun x : ℝ => x + MH * q) (add_mul MR MB q).symm
          _ = ((MR + MB) + MH) * q := by
            exact (add_mul (MR + MB) MH q).symm
          _ = (MR + (MB + MH)) * q := by
            exact congrArg (fun x : ℝ => x * q) (add_assoc MR MB MH)
      have hnorm :
          ‖L - B * Complex.I‖
            ≤ (MR + (MB + MH)) * q :=
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤ (MR + (MB + MH)) * q)
          hleft_error.symm
          (le_trans hsplit (le_trans hcomponent (le_of_eq hfactor)))
      hnorm)

/-- Owner analytic leaf: quantitative left-face residue tail for the `s = 1`
correction pole, with the standard contour normalization.

This is the non-circular one-pole input consumed by the right off-pole Cauchy
cancellation stack.  Its proof chain is the direct right off-pole tail, the
finite one-pole Cauchy residue identity, the positive-height standard residue
value, and the horizontal edge inverse-quadratic estimates.  It must not use
any theorem whose proof already depends on this left-face residue tail. -/
theorem zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eventual_inverseQuadratic_ownerResidueTail
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    ∃ ML : ℝ,
      0 < ML ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            ((2 * (Real.pi : ℂ) * Complex.I) *
              (-zetaCompletedExplicitFormulaPhi f (1 / 2))) * Complex.I‖
            ≤ ML *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let B : ℂ :=
    (2 * (Real.pi : ℂ) * Complex.I) *
      (-zetaCompletedExplicitFormulaPhi f (1 / 2))
  match
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eventual_inverseQuadratic_direct_ownerResidueTail
      f F h with
  | ⟨MR, hMRpos, hright⟩ =>
      match
        zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral_eventual_inverseQuadratic_of_standardResidue
          f F h with
      | ⟨MB, hMBpos, htangent⟩ =>
          match
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic_pos
              f F h with
          | ⟨MH, hMHpos, hhorizontal⟩ =>
              exact
                ⟨MR + (MB + MH),
                  add_pos hMRpos (add_pos hMBpos hMHpos),
                  zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral_eventual_inverseQuadratic_of_right_tangent_horizontal
                    f F h B MR MB MH hright htangent hhorizontal⟩

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
