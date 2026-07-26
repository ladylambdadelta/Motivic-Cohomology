import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffinePhysicalLimit
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.AutocorrelationAnalyticPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalScheduledBoundaryLimit

/-!
# Completed affine physical limit assembly

This file transports the completed affine full-line value through scheduled
rectangle exhaustion and normalized pole subtraction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open MeasureTheory
open scoped Topology

theorem zetaCompletedExplicitFormulaAutocorrelationCompletedAffineChannel_tendsto_physical_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction :=
      ZetaAdmissibleFunction.convolutionAutocorrelation f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    let analyticPackage :
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
      ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
          probe family (analyticPackage.height_schedule.height u))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel probe)) :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let regularFamily :
      ZetaAdmissibleFunction.ExplicitFormulaVerticallyRegularContourFamily :=
    ZetaAdmissibleFunction.CleanAutocorrelationVerticalRegularity.zetaCompletedExplicitFormula_autocorrelation_verticallyRegularContourFamily
      f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    regularFamily.toContourFamily
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let rightIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedRightAffineKernel_integrable_owner
      probe family analyticPackage
  let leftIntegrable :
      Integrable
        (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family)
        (volume : Measure ℝ) :=
    zetaCompletedLeftAffineKernel_integrable_of_verticallyRegular_owner
      probe regularFamily analyticPackage
  let rightLimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle (analyticPackage.height_schedule.height u)).T)
              (family.rectangle (analyticPackage.height_schedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t)
        atTop
        (𝓝
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family t)) :=
    ZetaAdmissibleFunction.explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family analyticPackage.height_schedule.height
      (ZetaAdmissibleFunction.zetaCompletedRightAffineKernel probe family)
      analyticPackage.height_schedule.cofinal rightIntegrable
  let leftLimit :
      Tendsto
        (fun u : ℝ =>
          ∫ t in Set.Icc
              (-(family.rectangle (analyticPackage.height_schedule.height u)).T)
              (family.rectangle (analyticPackage.height_schedule.height u)).T,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)
        atTop
        (𝓝
          (∫ t : ℝ,
            ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family t)) :=
    ZetaAdmissibleFunction.explicitFormulaScheduledRectangleWindowIntegral_tendsto_integral
      family analyticPackage.height_schedule.height
      (ZetaAdmissibleFunction.zetaCompletedLeftAffineKernel probe family)
      analyticPackage.height_schedule.cofinal leftIntegrable
  let differenceLimit := rightLimit.sub leftLimit
  let valueEquality :=
    zetaCompletedExplicitFormulaAutocorrelationCompletedAffineIntegral_eq_physical_owner
      f hPhi hLog
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            probe family (analyticPackage.height_schedule.height u))
        atTop
        (𝓝 target))
    valueEquality
    differenceLimit

/-- The geometric right-minus-left line expression is exactly the named
completed affine channel. -/
theorem zetaCompletedExplicitFormulaScheduledVerticalDifference_eq_completedAffineChannel
    (probe : ZetaAdmissibleFunction)
    (family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily)
    (analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family)
    (u : ℝ) :
    ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
          (family.rectangle (analyticPackage.height_schedule.height u)) -
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
          (family.rectangle (analyticPackage.height_schedule.height u)) =
      ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
        probe family (analyticPackage.height_schedule.height u) :=
  (zetaCompletedAffineVerticalChannel_eq_rightLineIntegral_sub_leftLineIntegral
    probe family (analyticPackage.height_schedule.height u)).symm

/-- Before normalization, the coupled completed affine contour tends to
`2 pi` times the affine physical subchannel. -/
theorem zetaCompletedExplicitFormulaAutocorrelationCompletedAffineVertical_tendsto_physical_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    let probe : ZetaAdmissibleFunction :=
      ZetaAdmissibleFunction.convolutionAutocorrelation f
    let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
      ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
    let analyticPackage :
        ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
      ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
        f
        (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
        hPhi
        hLog
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)) -
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)))
      atTop
      (𝓝
        (ZetaAdmissibleFunction.explicitFormulaTwoPi *
          zetaCompletedAffinePhysicalBoundaryChannel probe)) :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let channelLimit :=
    zetaCompletedExplicitFormulaAutocorrelationCompletedAffineChannel_tendsto_physical_owner
      f hPhi hLog
  let functionEquality :
      (fun u : ℝ =>
        ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u)) -
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
              (family.rectangle (analyticPackage.height_schedule.height u))) =
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedAffineVerticalChannel
            probe family (analyticPackage.height_schedule.height u)) :=
    funext
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaScheduledVerticalDifference_eq_completedAffineChannel
          probe family analyticPackage u)
  Eq.subst
    (motive := fun values : ℝ → ℂ =>
      Tendsto values atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi *
            zetaCompletedAffinePhysicalBoundaryChannel probe)))
    functionEquality.symm
    channelLimit

/-- The canonical normalized, pole-corrected completed affine contour tends to
the physical boundary minus the completed-pole residue packet.

The proof reflects the left completed face first, expands both resulting
right-half-plane completed logarithmic derivatives, applies von Mangoldt
Fourier inversion to their coupled arithmetic packet, and applies the direct
finite Abel--Plana formula to the coupled inverse-Gamma packet. -/
theorem zetaCompletedExplicitFormulaAutocorrelationNormalizedPoleCorrectedVertical_tendsto_completedBoundary_sub_poles_owner
    (f : ZetaAdmissibleFunction)
    (hPhi : ZetaAdmissibleFunction.ZetaPhiAnalyticControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f))
    (hLog : ZetaAdmissibleFunction.CompletedZetaNegLogDerivControl
      (ZetaAdmissibleFunction.convolutionAutocorrelation f)) :
    Tendsto
      (fun u : ℝ =>
        ZetaAdmissibleFunction.explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
          (ZetaAdmissibleFunction.convolutionAutocorrelation f)
          (ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
          (ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
            f
            (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
            hPhi
            hLog)
          u)
      atTop
      (𝓝
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))) :=
  let probe : ZetaAdmissibleFunction :=
    ZetaAdmissibleFunction.convolutionAutocorrelation f
  let family : ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
    ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f
  let analyticPackage :
      ZetaAdmissibleFunction.ExplicitFormulaFamilyAnalyticPackage probe family :=
    ZetaAdmissibleFunction.CleanAutocorrelationAnalyticPackage.zetaCompletedExplicitFormula_autocorrelation_familyAnalyticPackage
      f
      (ZetaAdmissibleFunction.zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
      hPhi
      hLog
  let poles : ℂ :=
    ZetaAdmissibleFunction.explicitFormulaRectangle_completedPoleResidueSum probe
  let boundary : ℂ := zetaCompletedAffinePhysicalBoundaryChannel probe
  let rawLimit :
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.zetaCompletedExplicitFormulaRightLineIntegral probe
                (family.rectangle (analyticPackage.height_schedule.height u)) -
            ZetaAdmissibleFunction.zetaCompletedExplicitFormulaLeftLineIntegral probe
                (family.rectangle (analyticPackage.height_schedule.height u)))
        atTop
        (𝓝
          (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary)) :=
    zetaCompletedExplicitFormulaAutocorrelationCompletedAffineVertical_tendsto_physical_owner
      f hPhi hLog
  let dividedLimit :=
    rawLimit.div_const ZetaAdmissibleFunction.explicitFormulaTwoPi
  let poleLimit :
      Tendsto (fun _u : ℝ => poles) atTop (𝓝 poles) :=
    tendsto_const_nhds
  let normalizedLimit := dividedLimit.sub poleLimit
  let divisionEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
          ZetaAdmissibleFunction.explicitFormulaTwoPi =
        boundary :=
    mul_div_cancel_left₀
      boundary
      ZetaAdmissibleFunction.explicitFormulaTwoPi_ne_zero
  let targetEquality :
      (ZetaAdmissibleFunction.explicitFormulaTwoPi * boundary) /
            ZetaAdmissibleFunction.explicitFormulaTwoPi - poles =
        zetaCompletedAffinePoleCorrectedBoundaryChannel probe :=
    Eq.trans
      (congrArg (fun value : ℂ => value - poles) divisionEquality)
      (zetaCompletedAffinePoleCorrectedBoundaryChannel_eq probe).symm
  Eq.subst
    (motive := fun target : ℂ =>
      Tendsto
        (fun u : ℝ =>
          ZetaAdmissibleFunction.explicitFormulaScheduledNormalizedPoleCorrectedVerticalDifference
            probe family analyticPackage u)
        atTop
        (𝓝 target))
    targetEquality
    normalizedLimit

end

end LFunctions
end Boundary
