import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleCauchyCancellation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.OnePoleHorizontalEdgeBounds

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

/-- Shared scheduled zero-excised strip data for the two horizontal edges, packaged from
an already constructed scheduled carrier and its top/bottom membership proofs. -/
theorem explicitFormulaHorizontalEdges_zeroExcisedStrip_of_mem
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ E : CompletedZetaZeroExcisedStrip
        (min F.c (1 - F.c)) (max F.c (1 - F.c)),
      (∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) ∧
      (∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) := by
  exact ⟨E, hTopMem, hBottomMem⟩

/-- The split horizontal edge envelope with exponents `(0, 2)` is bounded by a fixed
inverse-quadratic height envelope.

This is the deterministic normalization of the horizontal-edge owner envelope; no
top/bottom geometry is involved in this step. -/
theorem horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c))) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ T : ℝ,
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T
          ≤ B * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.logderiv_control.zeroExcisedStripBoundConstant
      (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0 *
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2)
        2 *
      horizontalEdgeLength F.c
  refine ⟨C + 1, add_pos_of_nonneg_of_pos ?_ zero_lt_one, ?_⟩
  · exact mul_nonneg
      (mul_nonneg
        (le_of_lt
          (h.logderiv_control.zeroExcisedStripBoundConstant_pos
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0))
        (le_of_lt
          (h.phi_control.verticalStripRapidDecayConstant_pos
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2)
            2)))
      (abs_nonneg ((1 - F.c) - F.c))
  · intro T
    let q : ℝ := (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))
    have hq_nonneg : 0 ≤ q := by
      exact le_of_lt (zpow_pos (one_add_norm_pos (F.rectangle T).T) (-(2 : ℤ)))
    have hC_le : C ≤ C + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hscaled : C * q ≤ (C + 1) * q :=
      mul_le_mul_of_nonneg_right hC_le hq_nonneg
    have hrewrite :
        horizontalUnorderedFamilyEdgeEnvelopeSplit
            h.phi_control h.logderiv_control F E 0 2 T =
          C * q := by
      have hraw :
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              h.phi_control h.logderiv_control F E 0 2 T =
            C *
              ((1 + ‖T‖) ^ (0 : ℕ) *
                (1 + ‖T‖) ^ (-(2 : ℤ))) := by
        exact horizontalEnvelopeSplit_reassociate
          (h.logderiv_control.zeroExcisedStripBoundConstant
            (min F.c (1 - F.c)) (max F.c (1 - F.c)) E 0)
          (h.phi_control.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2)
            2)
          (horizontalEdgeLength F.c)
          ((1 + ‖T‖) ^ (0 : ℕ))
          ((1 + ‖T‖) ^ (-(2 : ℤ)))
      have hpow_zero :
          (1 + ‖T‖) ^ (0 : ℕ) = (1 : ℝ) :=
        pow_zero (1 + ‖T‖)
      have hdecay_transport :
          (1 + ‖T‖) ^ (-(2 : ℤ)) = q := by
        rfl
      have hcollapse :
          (1 + ‖T‖) ^ (0 : ℕ) *
              (1 + ‖T‖) ^ (-(2 : ℤ)) =
            q := by
        calc
          (1 + ‖T‖) ^ (0 : ℕ) *
              (1 + ‖T‖) ^ (-(2 : ℤ)) =
              (1 : ℝ) * (1 + ‖T‖) ^ (-(2 : ℤ)) := by
            exact congrArg
              (fun x : ℝ => x * (1 + ‖T‖) ^ (-(2 : ℤ)))
              hpow_zero
          _ = (1 + ‖T‖) ^ (-(2 : ℤ)) := by
            exact one_mul ((1 + ‖T‖) ^ (-(2 : ℤ)))
          _ = q := by
            exact hdecay_transport
      exact Eq.trans hraw (congrArg (fun x : ℝ => C * x) hcollapse)
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ (C + 1) * q)
      hrewrite.symm
      hscaled

/-- Top horizontal-edge data sufficient to convert the existing split-envelope
estimate into the inverse-quadratic bound consumed by the vertical channel. -/
theorem explicitFormulaTopLineIntegral_inverseQuadraticEnvelope_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ Btop : ℝ,
        0 < Btop ∧
        ∀ T : ℝ,
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              h.phi_control h.logderiv_control F E 0 2 T
            ≤ Btop * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
    let envelopeData :=
      horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_owner
        f F h E
    exact Exists.elim envelopeData
      (fun B envelopeSpec =>
        ⟨B, envelopeSpec.1, envelopeSpec.2⟩)

/-- Bottom horizontal-edge data sufficient to convert the existing split-envelope
estimate into the inverse-quadratic bound consumed by the vertical channel. -/
theorem explicitFormulaBottomLineIntegral_inverseQuadraticEnvelope_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ Bbottom : ℝ,
        0 < Bbottom ∧
        ∀ T : ℝ,
          horizontalUnorderedFamilyEdgeEnvelopeSplit
              h.phi_control h.logderiv_control F E 0 2 T
            ≤ Bbottom * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ)) := by
    let envelopeData :=
      horizontalUnorderedFamilyEdgeEnvelopeSplit_zero_two_inverseQuadratic_owner
        f F h E
    exact Exists.elim envelopeData
      (fun B envelopeSpec =>
        ⟨B, envelopeSpec.1, envelopeSpec.2⟩)

/-- Scheduled top horizontal-edge inverse-quadratic estimate.

This is the top-edge half of the horizontal-control package.  It is separated
from the top-minus-bottom statement so the final owner theorem is only norm
subadditivity and scalar algebra. -/
theorem explicitFormulaTopLineIntegral_inverseQuadraticBound_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ Btop : ℝ,
        0 < Btop ∧
        ∀ u : ℝ,
          ‖zetaCompletedExplicitFormulaTopLineIntegral
              f (F.rectangle (h.height_schedule.height u))‖
            ≤ Btop *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let topData :=
      explicitFormulaTopLineIntegral_inverseQuadraticEnvelope_owner f F h E hTopMem
    exact Exists.elim topData
      (fun Btop topSpec =>
        ⟨Btop, topSpec.1,
          fun u =>
            have hedge :
                ‖zetaCompletedExplicitFormulaTopLineIntegral
                    f (F.rectangle (h.height_schedule.height u))‖
                  ≤ horizontalUnorderedFamilyEdgeEnvelopeSplit
                      h.phi_control h.logderiv_control F E 0 2
                      (h.height_schedule.height u) :=
              zetaCompletedExplicitFormulaTopLineIntegral_uIcc_norm_le_envelopeSplit
                h.phi_control h.logderiv_control
                (F.rectangle (h.height_schedule.height u)) E
                (fun x hx => hTopMem u x hx) 0 2
            le_trans hedge (topSpec.2 (h.height_schedule.height u))⟩)

/-- Scheduled bottom horizontal-edge inverse-quadratic estimate. -/
theorem explicitFormulaBottomLineIntegral_inverseQuadraticBound_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ Bbottom : ℝ,
        0 < Bbottom ∧
        ∀ u : ℝ,
          ‖zetaCompletedExplicitFormulaBottomLineIntegral
              f (F.rectangle (h.height_schedule.height u))‖
            ≤ Bbottom *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let bottomData :=
      explicitFormulaBottomLineIntegral_inverseQuadraticEnvelope_owner f F h E hBottomMem
    exact Exists.elim bottomData
      (fun Bbottom bottomSpec =>
        ⟨Bbottom, bottomSpec.1,
          fun u =>
            have hedge :
                ‖zetaCompletedExplicitFormulaBottomLineIntegral
                    f (F.rectangle (h.height_schedule.height u))‖
                  ≤ horizontalUnorderedFamilyEdgeEnvelopeSplit
                      h.phi_control h.logderiv_control F E 0 2
                      (h.height_schedule.height u) :=
              zetaCompletedExplicitFormulaBottomLineIntegral_uIcc_norm_le_envelopeSplit
                h.phi_control h.logderiv_control
                (F.rectangle (h.height_schedule.height u)) E
                (fun x hx => hBottomMem u x hx) 0 2
            le_trans hedge (bottomSpec.2 (h.height_schedule.height u))⟩)

/-- Norm-subadditivity and scalar accounting for the top-minus-bottom
horizontal estimate. -/
theorem explicitFormulaHorizontalSideDifference_inverseQuadraticBound_from_edges
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (Btop Bbottom : ℝ)
    (hBtop :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaTopLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Btop *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (hBbottom :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaBottomLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
          ≤ Bbottom *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖zetaCompletedExplicitFormulaTopLineIntegral
            f (F.rectangle (h.height_schedule.height u)) -
          zetaCompletedExplicitFormulaBottomLineIntegral
            f (F.rectangle (h.height_schedule.height u))‖
        ≤ (Btop + Bbottom) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  let T : ℝ := h.height_schedule.height u
  let q : ℝ := (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))
  have hnorm :
      ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
        ≤
          ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ +
            ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖ :=
    norm_sub_le
      (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
  have hedges :
      ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)‖ +
          ‖zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
        ≤ Btop * q + Bbottom * q :=
    add_le_add (hBtop u) (hBbottom u)
  have hcombine :
      Btop * q + Bbottom * q = (Btop + Bbottom) * q :=
    (add_mul Btop Bbottom q).symm
  exact le_trans (le_trans hnorm hedges) (le_of_eq hcombine)

/-- Horizontal-edge inverse-quadratic cancellation estimate for the scheduled
top-minus-bottom horizontal side difference.

This is the horizontal estimate consumed by the correction-channel users. -/
theorem explicitFormulaHorizontalSideDifference_inverseQuadraticBound_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ B : ℝ,
        0 < B ∧
        ∀ u : ℝ,
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
            ≤ B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let topData :=
      explicitFormulaTopLineIntegral_inverseQuadraticBound_owner f F h E hTopMem
    let bottomData :=
      explicitFormulaBottomLineIntegral_inverseQuadraticBound_owner f F h E hBottomMem
    exact Exists.elim topData
      (fun Btop topSpec =>
        Exists.elim bottomData
          (fun Bbottom bottomSpec =>
            ⟨Btop + Bbottom, add_pos topSpec.1 bottomSpec.1,
              explicitFormulaHorizontalSideDifference_inverseQuadraticBound_from_edges
                f F h Btop Bbottom topSpec.2 bottomSpec.2⟩))

/-- Inserting the package height schedule into the unscheduled horizontal
inverse-quadratic estimate gives the scheduled estimate. -/
theorem explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_of_unscheduled
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (B : ℝ)
    (hB :
      ∀ T : ℝ,
        ‖zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T)‖
          ≤ B * (1 + ‖(F.rectangle T).T‖) ^ (-(2 : ℤ))) :
    ∀ u : ℝ,
      ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
        ≤ B *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  intro u
  exact hB (h.height_schedule.height u)

/-- Shared scheduled horizontal-edge inverse-quadratic cancellation estimate.

Both off-pole correction faces consume the same top-minus-bottom horizontal
side difference, so the face-specific estimates below are wrappers over this
single scheduled transport of the horizontal owner estimate. -/
theorem explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      ∃ B : ℝ,
        0 < B ∧
        ∀ u : ℝ,
          ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
            ≤ B *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let horizontalData :=
      explicitFormulaHorizontalSideDifference_inverseQuadraticBound_owner
        f F h E hTopMem hBottomMem
    exact Exists.elim horizontalData
      (fun B horizontalSpec =>
        ⟨B, horizontalSpec.1, horizontalSpec.2⟩)

/-- Exported scheduled horizontal decay once both horizontal edges are carried by
a common zero-excised strip. -/
theorem explicitFormulaScheduledHorizontalSideDifference_tendsto_zero_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
      Tendsto
        (fun u : ℝ => explicitFormulaScheduledHorizontalSideDifference f F h u)
        atTop
        (𝓝 0) := by
    let scheduledData :=
      explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_owner
        f F h E hTopMem hBottomMem
    exact Exists.elim scheduledData
      (fun B scheduledSpec =>
        have hbound :
            ∀ᶠ u in atTop,
              ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
                ≤ B *
                  (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
          Filter.Eventually.of_forall scheduledSpec.2
        have hmajorant :
            Tendsto
              (fun u : ℝ =>
                B *
                  (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
              atTop
              (𝓝 0) :=
          zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
            F h.height_schedule B
        squeeze_zero_norm' hbound hmajorant)

/-- Horizontal-edge cancellation for the scheduled right-face opposite-pole
integral.  This is the decay of the horizontal remainder exposed by the Cauchy
rectangle identity, not a vertical pointwise denominator estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_horizontalEdgeCancellation_inverseQuadraticBound_owner
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ u : ℝ,
        ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
          ≤ B *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    explicitFormulaScheduledHorizontalSideDifference_inverseQuadraticBound_owner
      f F h E hTopMem hBottomMem

/-- Algebraic assembly of the scheduled Cauchy rectangle cancellation and the
horizontal-edge inverse-quadratic bound for the right-face off-pole pole. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_inverseQuadraticBound_from_cauchyHorizontal_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
        ∀ᶠ u in atTop,
          ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
            f F h u‖
            ≤ M *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let rectangleData :=
      zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledRectangleCauchyCancellation_owner
        f F h A hApos htangent
    let horizontalData :=
      zetaCompletedExplicitFormulaCorrectionRightOnePole_horizontalEdgeCancellation_inverseQuadraticBound_owner
        f F h E hTopMem hBottomMem
    exact Exists.elim rectangleData
      (fun Arect rectangleSpec =>
        Exists.elim horizontalData
          (fun B horizontalSpec =>
            ⟨Arect + B, add_pos rectangleSpec.1 horizontalSpec.1,
              rectangleSpec.2.mono
                (fun u hrectangle =>
                  let q : ℝ :=
                    (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
                  have hhorizontal :
                      ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖
                        ≤ B * q :=
                    horizontalSpec.2 u
                  have hcombined :
                      ‖explicitFormulaScheduledHorizontalSideDifference f F h u‖ + Arect * q
                        ≤ B * q + Arect * q :=
                    add_le_add_right hhorizontal (Arect * q)
                  have hcommuted :
                      B * q + Arect * q = Arect * q + B * q :=
                    add_comm (B * q) (Arect * q)
                  have hfactored :
                      Arect * q + B * q = (Arect + B) * q :=
                    (add_mul Arect B q).symm
                  have htarget :
                      B * q + Arect * q = (Arect + B) * q :=
                    Eq.trans hcommuted hfactored
                  le_trans hrectangle (le_trans hcombined (le_of_eq htarget)))⟩))

/-- The scheduled Cauchy/oscillatory cancellation package for the right-face
off-pole `s = 1` correction integral.

The proof is now localized to the finite Cauchy rectangle cancellation, the
horizontal-edge cancellation estimate, and the final inverse-quadratic algebra. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledContourCancellation_inverseQuadraticBound_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
          f F h u‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePole_inverseQuadraticBound_from_cauchyHorizontal_owner
      f F h A hApos htangent E hTopMem hBottomMem

/-- Scheduled Cauchy cancellation for the explicit right-face off-pole `s = 1`
correction integral.

The right edge has fixed real part, so this estimate is not a consequence of a
pointwise denominator-separation bound on an expanding interval.  Its analytic
content is the contour/oscillatory cancellation that converts the off-pole
vertical integral into an inverse-quadratic scheduled tail.  The following
named-integral theorem only unfolds the owner definition. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_inverseQuadraticBound_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ᶠ u in atTop,
        ‖∫ t in
            Set.Icc
              (-(F.rectangle (h.height_schedule.height u)).T)
              (F.rectangle (h.height_schedule.height u)).T,
            (-1 /
                (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1)) *
              zetaCompletedExplicitFormulaPhi f
                (zetaCompletedExplicitFormulaRightPath
                    (F.rectangle (h.height_schedule.height u)) t - 1 / 2)‖
            ≤ M *
              (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
    let contourData :=
      zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledContourCancellation_inverseQuadraticBound_owner
        f F h A hApos htangent E hTopMem hBottomMem
    exact Exists.elim contourData
      (fun M contourSpec =>
        ⟨M, contourSpec.1,
          contourSpec.2.mono
            (fun u hu =>
              have hnamed :
                  (∫ t in
                      Set.Icc
                        (-(F.rectangle (h.height_schedule.height u)).T)
                        (F.rectangle (h.height_schedule.height u)).T,
                      (-1 /
                          (zetaCompletedExplicitFormulaRightPath
                              (F.rectangle (h.height_schedule.height u)) t - 1)) *
                        zetaCompletedExplicitFormulaPhi f
                          (zetaCompletedExplicitFormulaRightPath
                              (F.rectangle (h.height_schedule.height u)) t - 1 / 2)) =
                    zetaCompletedExplicitFormulaCorrectionRightOnePoleScheduledOscillatoryIntegral
                      f F h u :=
                zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_eq_named
                  f F h u
              Eq.symm hnamed ▸ hu)⟩)

/-- Definition transport from the right-face off-pole correction integral to its
explicit oscillatory-integral cancellation estimate. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePole_scheduledOscillatoryIntegral_inverseQuadraticBound_owner
      f F h A hApos htangent E hTopMem hBottomMem

/-- Algebraic transport from the scheduled right-face Cauchy cancellation estimate
to the public inverse-quadratic off-pole bound.  The only remaining content of
the preceding theorem is the scheduled contour cancellation itself. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_rawInverseQuadraticBound_owner
      f F h A hApos htangent E hTopMem hBottomMem

/-- Off-pole right-face correction tail estimate for the `s = 1` pole.

This public estimate is a thin wrapper over the scheduled Cauchy cancellation
theorem.  It deliberately does not assert that pointwise denominator separation
alone controls the expanding vertical integral. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_offPoleTailBound_owner
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
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
    (E : CompletedZetaZeroExcisedStrip
      (min F.c (1 - F.c)) (max F.c (1 - F.c)))
    (hTopMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaTopPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier)
    (hBottomMem :
      ∀ (u x : ℝ), x ∈ Set.uIcc F.c (1 - F.c) →
        zetaCompletedExplicitFormulaBottomPath
          (F.rectangle (h.height_schedule.height u)) x ∈ E.carrier) :
    ∃ M : ℝ,
      0 < M ∧
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  exact
    zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_scheduledCauchyCancellation_inverseQuadraticBound_owner
      f F h A hApos htangent E hTopMem hBottomMem

/-- The off-pole right-face correction tail majorant tends to zero along the
cofinal scheduled heights. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tailMajorant_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  exact
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule M

/-- The right-face opposite-pole correction integral vanishes by the off-pole
denominator bound and rapid vertical-strip decay of the test transform. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_offPoleTailBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (M : ℝ)
    (hbound :
      ∀ u : ℝ,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    squeeze_zero_norm hbound
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tailMajorant_tendsto_zero
        f F h M)

/-- Eventual off-pole right-face correction tail bounds are enough for the
scheduled right one-pole vertical integral to vanish.  This is the asymptotic
form actually used by contour transport; a global all-height inverse-quadratic
bound is a stronger compact-initial-segment statement. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_eventualOffPoleTailBound
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (M : ℝ)
    (hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u)‖
          ≤ M *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
          f F (h.height_schedule.height u))
      atTop
      (𝓝 0) := by
  exact
    squeeze_zero_norm' hbound
      (zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tailMajorant_tendsto_zero
        f F h M)

/-- Right-face one-pole Cauchy limit for the opposite `s = 1` pole contribution. -/
theorem zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_eventualTangentBound
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
    Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 0) := by
    let stripData :=
      ExplicitFormulaFamilyAnalyticPackage.scheduled_horizontalFamilyZeroExcisedStrip
        h
    exact Exists.elim stripData
      (fun E stripSpec =>
        let tailData :=
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_offPoleTailBound_owner
            f F h A hApos htangent E stripSpec.1 stripSpec.2
        Exists.elim tailData
          (fun C tailSpec =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_tendsto_zero_of_eventualOffPoleTailBound
              f F h C tailSpec.2))

/-- A pointwise bound on the top `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- A pointwise bound on the bottom `s = 0` single-pole horizontal integrand
controls the corresponding horizontal edge integral. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T C : ℝ)
    (hC :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖ ≤ C) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤ C * horizontalEdgeLength F.c := by
  exact
    norm_setIntegral_uIcc_le_horizontalEdgeLength_mul
      (fun x : ℝ =>
        (-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
          zetaCompletedExplicitFormulaPhi f
            (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2))
      F.c C hC

/-- Pointwise top-edge decay for the isolated `s = 0` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_of_nonneg_right hinv (norm_nonneg b)
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaTopPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaTopPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaTopPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Pointwise bottom-edge decay for the isolated `s = 0` horizontal integrand once
the pole denominator is bounded by one. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hinv :
      ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖(-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)‖
      ≤
        hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) := by
  let a : ℂ := -1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
  let b : ℂ :=
    zetaCompletedExplicitFormulaPhi f
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
  have hproduct : ‖a * b‖ ≤ ‖b‖ := by
    calc
      ‖a * b‖ = ‖a‖ * ‖b‖ := by
        exact norm_mul a b
      _ ≤ 1 * ‖b‖ := by
        exact mul_le_mul_of_nonneg_right hinv (norm_nonneg b)
      _ = ‖b‖ := by
        exact one_mul ‖b‖
  have hstrip :
      min F.c (1 - F.c) - 1 / 2
          ≤ (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re ∧
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2 : ℂ).re
          ≤ max F.c (1 - F.c) - 1 / 2 :=
    zetaCompletedExplicitFormulaBottomPath_shift_re_mem_uIcc_bounds
      (F.rectangle T) x hx
  have hphi :
      ‖b‖
        ≤
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
          (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)) :=
    (hPhi.verticalStripRapidDecayConstant_bound
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) N
        (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x - 1 / 2)
        hstrip.1 hstrip.2).trans_eq
      (congrArg
        (fun u : ℝ =>
          hPhi.verticalStripRapidDecayConstant
            (min F.c (1 - F.c) - 1 / 2)
            (max F.c (1 - F.c) - 1 / 2) N *
            (1 + u) ^ (-(N : ℤ)))
        (zetaCompletedExplicitFormulaBottomPath_shift_im_norm (F.rectangle T) x))
  exact le_trans hproduct hphi

/-- Top `s = 0` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Bottom `s = 0` horizontal edge bound obtained from denominator separation and
`Φ_f` vertical-strip decay. -/
theorem zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily) (T : ℝ)
    (hinv :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_of_pointwise
      f F T
      (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ)))
      (fun x hx =>
        zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegrand_norm_le_phiDecay_of_inv_le_one
          f hPhi F T x hx (hinv x hx) N)

/-- Isolated scheduled `s = 0` horizontal remainder bound from the two
single-pole horizontal edge estimates. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hinvTop :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaTopPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (hinvBottom :
      ∀ x : ℝ, x ∈ Set.uIcc F.c (1 - F.c) →
        ‖-1 /
          zetaCompletedExplicitFormulaBottomPath
            (F.rectangle (h.height_schedule.height u)) x‖ ≤ 1)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  let T : ℝ := h.height_schedule.height u
  let C : ℝ :=
    hPhi.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) N *
    (1 + ‖(F.rectangle T).T‖) ^ (-(N : ℤ))
  have htop :
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T hinvTop N
  have hbottom :
      ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c :=
    zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral_norm_le_phiDecay_of_inv_le_one
      f hPhi F T hinvBottom N
  have hedges :
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤
          ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
          ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖ :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_edges
      f F h u
  have hsum :
      ‖zetaCompletedExplicitFormulaCorrectionTopZeroPoleHorizontalIntegral f F T‖ +
        ‖zetaCompletedExplicitFormulaCorrectionBottomZeroPoleHorizontalIntegral f F T‖
        ≤ C * horizontalEdgeLength F.c + C * horizontalEdgeLength F.c :=
    add_le_add htop hbottom
  exact le_trans hedges hsum

/-- The top horizontal `s = 0` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaTopPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaTopPath (F.rectangle T) x
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaTopPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- The bottom horizontal `s = 0` pole denominator is separated once the rectangle
height has norm at least one. -/
theorem zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height
    (F : ExplicitFormulaContourFamily) (T x : ℝ)
    (hT : 1 ≤ ‖(F.rectangle T).T‖) :
    ‖-1 / zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x‖ ≤ 1 := by
  let z : ℂ := zetaCompletedExplicitFormulaBottomPath (F.rectangle T) x
  have him_le_norm : ‖(F.rectangle T).T‖ ≤ ‖z‖ := by
    have him_abs_le : |z.im| ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    have him_norm_le : ‖z.im‖ ≤ ‖z‖ := by
      calc
        ‖z.im‖ = |z.im| := by
          exact Real.norm_eq_abs z.im
        _ ≤ Complex.abs z := him_abs_le
        _ = ‖z‖ := by
          exact (Complex.norm_eq_abs z).symm
    have him_eq : ‖z.im‖ = ‖(F.rectangle T).T‖ :=
      zetaCompletedExplicitFormulaBottomPath_im_norm (F.rectangle T) x
    exact Eq.subst
      (motive := fun q : ℝ => q ≤ ‖z‖)
      him_eq
      him_norm_le
  have hone_le_norm : 1 ≤ ‖z‖ :=
    le_trans hT him_le_norm
  have hnorm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hone_le_norm
  have hdiv :
      ‖-1 / z‖ = 1 / ‖z‖ := by
    calc
      ‖-1 / z‖ = ‖(-1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (-1 : ℂ) z
      _ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) (norm_neg (1 : ℂ))
      _ = 1 / ‖z‖ := by
        exact congrArg (fun q : ℝ => q / ‖z‖) norm_one
  have hdiv_le : 1 / ‖z‖ ≤ 1 := by
    calc
      1 / ‖z‖ ≤ 1 / (1 : ℝ) := by
        exact one_div_le_one_div_of_le zero_lt_one hone_le_norm
      _ = 1 := by
        exact div_one (1 : ℝ)
  exact Eq.subst
    (motive := fun q : ℝ => q ≤ 1)
    hdiv.symm
    hdiv_le

/-- Scheduled isolated `s = 0` horizontal remainder bound at heights where the
horizontal pole denominators are separated by the height. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    (hT : 1 ≤ ‖(F.rectangle (h.height_schedule.height u)).T‖)
    (N : ℕ) :
    ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
      ≤
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c +
        (hPhi.verticalStripRapidDecayConstant
          (min F.c (1 - F.c) - 1 / 2)
          (max F.c (1 - F.c) - 1 / 2) N *
        (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(N : ℤ))) *
          horizontalEdgeLength F.c := by
  exact
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_inv_le_one
      f hPhi F h u
      (fun x hx =>
        zetaCompletedExplicitFormulaTopPath_zeroPoleInv_norm_le_one_of_one_le_height
          F (h.height_schedule.height u) x hT)
      (fun x hx =>
        zetaCompletedExplicitFormulaBottomPath_zeroPoleInv_norm_le_one_of_one_le_height
          F (h.height_schedule.height u) x hT)
      N

/-- The isolated scheduled `s = 0` horizontal remainder is eventually bounded by
an inverse-quadratic height envelope. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    let C : ℝ :=
      h.phi_control.verticalStripRapidDecayConstant
        (min F.c (1 - F.c) - 1 / 2)
        (max F.c (1 - F.c) - 1 / 2) 2
    let L : ℝ := horizontalEdgeLength F.c
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  change
    ∀ᶠ u in atTop,
      ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
        ≤ (C * L + C * L) *
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
  exact
    (h.height_schedule.eventually_one_le_rectangle_height_norm).mono
      (fun u hT =>
        let q : ℝ :=
          (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ))
        have hraw :
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖
              ≤ C * q * L + C * q * L :=
          zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_norm_le_phiDecay_of_one_le_height
            f h.phi_control F h u hT 2
        have hedge :
            C * q * L = C * L * q := by
          calc
            C * q * L = (C * q) * L := by
              rfl
            _ = C * (q * L) := by
              exact mul_assoc C q L
            _ = C * (L * q) := by
              exact congrArg (fun x : ℝ => C * x) (mul_comm q L)
            _ = C * L * q := by
              exact (mul_assoc C L q).symm
        have hsum :
            C * q * L + C * q * L = (C * L + C * L) * q := by
          calc
            C * q * L + C * q * L = C * L * q + C * L * q := by
              exact congrArg₂ (fun x y : ℝ => x + y) hedge hedge
            _ = (C * L + C * L) * q := by
              exact (add_mul (C * L) (C * L) q).symm
        Eq.subst
          (motive := fun x : ℝ =>
            ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference
                f F h u‖ ≤ x)
          hsum
          hraw)

/-- The isolated scheduled `s = 0` horizontal remainder tends to zero. -/
theorem zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u)
      atTop
      (𝓝 0) := by
  let C : ℝ :=
    h.phi_control.verticalStripRapidDecayConstant
      (min F.c (1 - F.c) - 1 / 2)
      (max F.c (1 - F.c) - 1 / 2) 2
  let L : ℝ := horizontalEdgeLength F.c
  have hbound :
      ∀ᶠ u in atTop,
        ‖zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference f F h u‖
          ≤ (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)) :=
    zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_eventually_norm_le_inverseQuadratic
      f F h
  have hmajorant :
      Tendsto
        (fun u : ℝ =>
          (C * L + C * L) *
            (1 + ‖(F.rectangle (h.height_schedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero
      F h.height_schedule (C * L + C * L)
  exact squeeze_zero_norm' hbound hmajorant

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
