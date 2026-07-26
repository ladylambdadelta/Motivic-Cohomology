import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.CoreInputs
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PhysicalBoundaryIdentificationCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.PositivityBridgeSummedPrime

namespace Boundary
namespace LFunctions

noncomputable section

open Filter
open scoped Topology

/-- Trace-Bessel summed-prime transport gives the Weil positivity input
directly from the boundary identification. -/
theorem finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel_core
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ZetaWeilQuadraticPositivity :=
  zetaWeilQuadraticPositivity_of_traceBesselSummedPrimeTransport_owner
    zetaWeilQuadraticPositivity_canonicalBranch
    zetaWeilQuadraticPositivity_canonicalPartialOneTwo
    zetaWeilQuadraticPositivity_canonicalCompactOneTwo
    zetaWeilQuadraticPositivity_canonicalRightCriticalGrowth
    zetaWeilQuadraticPositivity_canonicalPartialLeft
    zetaWeilQuadraticPositivity_canonicalCompactBoundary
    hBoundary

theorem finalRiemannHypothesis_canonicalPoleClearedRightCriticalStripAdmissibleGrowth_core :
    PoleClearedRightCriticalStripAdmissibleGrowth :=
  finalRiemannHypothesis_poleClearedRightCriticalStripAdmissibleGrowth
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_owner

theorem finalRiemannHypothesis_canonicalZeroTailSmallValuesOwnerRunge_core :
    ZeroTailSmallValuesOwnerRunge :=
  finalRiemannHypothesis_separatedZeroTailSmallValuesOwnerRunge
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
    boundaryLineOneAbelPartialMajorant_from_realParam
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
    finalRiemannHypothesis_canonicalPoleClearedRightCriticalStripAdmissibleGrowth_core
    (reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      boundaryLineOneAbelPartialMajorant_from_realParam)
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact

theorem finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity_core
    (hPositive : ZetaWeilQuadraticPositivity) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  let hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption :=
    Complex.binetSecondFormulaBranchUniformTailAbsorption_owner
  let hpartialOneTwo : BoundaryLineOneAbelPartialMajorant :=
    boundaryLineOneAbelPartialMajorant_from_realParam
  let hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound :=
    poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact
  let hgrowth : PoleClearedRightCriticalStripAdmissibleGrowth :=
    finalRiemannHypothesis_canonicalPoleClearedRightCriticalStripAdmissibleGrowth_core
  let hpartialLeft : ReflectedBoundaryAbelPartialMajorant :=
    reflectedBoundaryAbelPartialMajorant_of_boundaryLineOneAbelPartialMajorant
      hpartialOneTwo
  let hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound :=
    poleClearedRightCriticalStripCompactBoundaryBound_from_compact
  let hZeroTail : ZeroTailSmallValuesOwnerRunge :=
    finalRiemannHypothesis_canonicalZeroTailSmallValuesOwnerRunge_core
  centeredZeroCriterion_of_zetaWeilQuadraticPositivity
    hZeroTail
    hbranch
    hpartialOneTwo
    hcompactOneTwo
    hgrowth
    hpartialLeft
    hcompactBoundary
    hPositive

/-- Trace-Bessel summed-prime transport gives the centered-zero criterion
directly from the boundary identification. -/
theorem finalRiemannHypothesis_centeredZeroCriterion_traceBessel_core
    (hBoundary : ZetaWeilAutocorrelationBoundaryIdentification) :
    ∀ s : ℂ,
      riemannZeta (1 / 2 + s) = 0 →
        (¬ ∃ n : ℕ, 1 / 2 + s = -2 * (n + 1)) →
          (1 / 2 + s) ≠ 1 →
            s.re = 0 :=
  finalRiemannHypothesis_centeredZeroCriterion_of_zetaWeilQuadraticPositivity_core
    (finalRiemannHypothesis_zetaWeilQuadraticPositivity_traceBessel_core
      hBoundary)

end
end LFunctions
end Boundary
