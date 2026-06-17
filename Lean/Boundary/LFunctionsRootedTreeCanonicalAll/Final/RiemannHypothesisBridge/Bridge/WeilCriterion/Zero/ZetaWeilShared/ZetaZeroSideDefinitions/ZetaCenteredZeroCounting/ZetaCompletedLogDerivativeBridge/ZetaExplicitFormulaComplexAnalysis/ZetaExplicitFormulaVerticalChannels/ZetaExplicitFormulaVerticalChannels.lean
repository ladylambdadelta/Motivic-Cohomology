import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ZetaExplicitFormulaAnalyticPackage
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaGeometry.ZetaExplicitFormulaGeometry
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaLogDerivative.ZetaExplicitFormulaLogDerivative
import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaResidueRegularity.ZetaExplicitFormulaResidueRegularity
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Boundary explicit-formula vertical channel owner API

This file owns the vertical realization of the prime, archimedean, and
correction channel packets.  The scheduled contour is the analytic
normalization procedure: it transports a chosen vertical measurement into the
completed boundary-channel object.  The complex-analysis contour assembly file
imports these channel objects and treats the corresponding transport theorems
as owner facts.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The prime logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaPrimeVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaPrimeLogDerivative (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The archimedean logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaArchimedeanLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaArchimedeanLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The pole-correction logarithmic-derivative vertical channel. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  (∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
    explicitFormulaCorrectionLogDerivative
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t) *
      zetaCompletedExplicitFormulaPhi f
        (zetaCompletedExplicitFormulaRightPath (F.rectangle T) t - 1 / 2)) -
    ∫ t in Set.Icc (-(F.rectangle T).T) (F.rectangle T).T,
      explicitFormulaCorrectionLogDerivative
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t) *
        zetaCompletedExplicitFormulaPhi f
          (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) t - 1 / 2)

/-- The sum of the three vertical logarithmic-derivative channels. -/
noncomputable def zetaCompletedExplicitFormulaVerticalChannelSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaPrimeVerticalChannel f F T +
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F T +
      zetaCompletedExplicitFormulaCorrectionVerticalChannel f F T

/-! ## Scheduled channel transport consumers -/

/-- Prime scheduled vertical contour transport to the completed prime channel.

This consumer is downstream of the acyclic finite rectangle residue owner theorem. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u) :=
    fun u =>
      zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerCauchyResidueComputation
        f F.toContourFamily h (h.height_schedule.height u)
        (h.height_schedule.avoids_boundary u)
  sorry

/-- The scheduled prime vertical contour realization transports to the completed prime
GNS/defect-kernel channel. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeGNSDefectKernelChannel_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeContribution_ownerPrimeVerticalTransport
      f F hSchedule

/-- The scheduled prime vertical contour realization transports to the completed prime
boundary channel. -/
theorem explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_completedPrimeChannel_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  dsimp
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_primeGNSDefectKernelChannel_ownerPrimeTransportComparison
      f F hSchedule

/-- Prime vertical-channel comparison with the prime boundary contribution, owned by the
prime transport/distribution layer. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeTransportComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  dsimp
  exact
    explicitFormulaScheduledPrimeVerticalContourRealization_tendsto_completedPrimeChannel_ownerPrimeTransportComparison
      f F hSchedule

/-- Prime vertical-channel convergence, owned by the prime channel normalization/transport. -/
theorem zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaPrimeVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaPrimeContribution f)) := by
  dsimp
  exact
    zetaCompletedExplicitFormulaPrimeVerticalChannel_tendsto_primeContribution_ownerPrimeTransportComparison
      f F hSchedule

/-- Archimedean scheduled vertical contour transport to the completed archimedean channel. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u) :=
    fun u =>
      zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerCauchyResidueComputation
        f F.toContourFamily h (h.height_schedule.height u)
        (h.height_schedule.avoids_boundary u)
  sorry

/-- The scheduled archimedean vertical contour realization transports to the completed
archimedean boundary channel. -/
theorem explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_completedArchimedeanChannel_ownerArchimedeanNormalizationComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  exact
    explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_archimedeanContribution_ownerArchimedeanVerticalTransport
      f F hSchedule

/-- Archimedean vertical-channel comparison with the archimedean boundary contribution,
owned by the completed normalization layer. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanNormalizationComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  dsimp
  exact
    explicitFormulaScheduledArchimedeanVerticalContourRealization_tendsto_completedArchimedeanChannel_ownerArchimedeanNormalizationComparison
      f F hSchedule

/-- Archimedean vertical-channel convergence, owned by the archimedean normalization. -/
theorem zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaArchimedeanVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaArchimedeanContribution f)) := by
  dsimp
  exact
    zetaCompletedExplicitFormulaArchimedeanVerticalChannel_tendsto_archimedeanContribution_ownerArchimedeanNormalizationComparison
      f F hSchedule

/-- Correction scheduled vertical contour transport to the completed correction channel. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalTransport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  dsimp
  let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
  have hresidue :
      ∀ u : ℝ,
        zetaCompletedExplicitFormulaContourIntegral f
            (F.toContourFamily.rectangle (h.height_schedule.height u)) =
          explicitFormulaCompletedZeroHeightWindowResidueSum f
            (h.height_schedule.height u) :=
    fun u =>
      zetaCompletedExplicitFormulaRectangleContourIntegral_eq_heightWindowResidueSum_of_avoidsBoundary_ownerCauchyResidueComputation
        f F.toContourFamily h (h.height_schedule.height u)
        (h.height_schedule.avoids_boundary u)
  sorry

/-- The scheduled pole-correction vertical contour realization transports to the completed
correction boundary channel. -/
theorem explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_completedCorrectionChannel_ownerPoleCorrectionComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  exact
    explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_correctionContribution_ownerCorrectionVerticalTransport
      f F hSchedule

/-- Correction vertical-channel comparison with the correction boundary contribution, owned
by the pole-correction normalization layer. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerPoleCorrectionComparison
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  dsimp
  exact
    explicitFormulaScheduledCorrectionVerticalContourRealization_tendsto_completedCorrectionChannel_ownerPoleCorrectionComparison
      f F hSchedule

/-- Correction vertical-channel convergence, owned by the pole-correction normalization. -/
theorem zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerCorrectionVerticalChannel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaVerticallyRegularContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F.toContourFamily) :
    let h := explicitFormulaFamilyAnalyticPackage_of_admissible f F hSchedule
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionVerticalChannel f F.toContourFamily
          (h.height_schedule.height u))
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionContribution f)) := by
  dsimp
  exact
    zetaCompletedExplicitFormulaCorrectionVerticalChannel_tendsto_correctionContribution_ownerPoleCorrectionComparison
      f F hSchedule

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
