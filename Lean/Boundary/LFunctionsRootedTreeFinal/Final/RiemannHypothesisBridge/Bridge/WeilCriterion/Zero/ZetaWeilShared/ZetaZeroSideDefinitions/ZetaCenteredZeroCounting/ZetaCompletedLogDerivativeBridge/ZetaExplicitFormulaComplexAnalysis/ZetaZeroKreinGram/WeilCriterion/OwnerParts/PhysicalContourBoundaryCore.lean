import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CompletedAffinePhysicalBoundaryCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.RightHalfPlaneGrowth.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.TailSummability.Owner

/-!
# Selector-free physical contour boundary core

This file owns the physical boundary propositions and autocorrelation contour
coordinates without selecting a canonical avoiding-height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Boundary identification needed by the Weil-positivity bridge on autocorrelation probes. -/
def ZetaWeilAutocorrelationBoundaryIdentification : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (zetaCompletedAffinePoleCorrectedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- Completed-boundary identification in the endpoint-absorption coordinates
used by the positivity owner. -/
def ZetaWeilAutocorrelationCompletedBoundaryIdentification : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    zetaWeilFormCompleted
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      Complex.re
        (ZetaAdmissibleFunction.completedBoundaryChannel
          (ZetaAdmissibleFunction.convolutionAutocorrelation f))

/-- Zero-side identification needed before taking real parts in the Weil bridge. -/
def ZetaCompletedAutocorrelationZeroSideBoundaryIdentification : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    Boundary.LFunctions.zetaCompletedZeroSideComplex
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) =
      zetaCompletedAffinePoleCorrectedBoundaryChannel
        (ZetaAdmissibleFunction.convolutionAutocorrelation f)

/-- Common scheduled-contour limit statement before uniqueness of limits is applied. -/
def ZetaCompletedAutocorrelationPoleCorrectedCommonLimit : Prop :=
  ∀ f : ZetaAdmissibleFunction,
    ∃ φ : ℝ → ℂ,
      Tendsto φ atTop
        (𝓝
          (Boundary.LFunctions.zetaCompletedZeroSideComplex
            (ZetaAdmissibleFunction.convolutionAutocorrelation f))) ∧
      Tendsto φ atTop
        (𝓝
          (zetaCompletedAffinePoleCorrectedBoundaryChannel
            (ZetaAdmissibleFunction.convolutionAutocorrelation f)))

/-- The autocorrelation probe used by the physical completed contour. -/
def zetaAutocorrelationPhysicalProbe
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction :=
  ZetaAdmissibleFunction.convolutionAutocorrelation f

/-- The completed contour family attached to an autocorrelation probe. -/
def zetaAutocorrelationPhysicalContourFamily
    (f : ZetaAdmissibleFunction) :
    ZetaAdmissibleFunction.ExplicitFormulaContourFamily :=
  ZetaAdmissibleFunction.zetaCompletedExplicitFormula_autocorrelation_contourFamily f

/- The physical owner assembles the analytic inputs only after the tail layer;
   keeping this package here avoids introducing an upward import into that layer. -/
theorem summable_zetaZeroSideContribution_owner
    (φ : ZetaAdmissibleFunction) :
    Summable
      (fun ρ : {ρ : ℂ // ZetaCompletedZero ρ} =>
        zetaZeroSideContribution (ρ : ℂ) φ) := by
  exact summable_zetaZeroSideContribution
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    boundaryLineOneAbelPartialMajorant_from_realParam
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    (poleClearedRightCriticalStripAdmissibleGrowth_owner
      Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
      poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner)
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
    φ

end

end LFunctions
end Boundary
