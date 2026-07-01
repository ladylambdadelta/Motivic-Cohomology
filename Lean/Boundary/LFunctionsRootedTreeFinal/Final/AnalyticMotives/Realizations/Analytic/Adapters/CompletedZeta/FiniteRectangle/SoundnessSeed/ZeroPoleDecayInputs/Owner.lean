import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleVerticalTransport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLeftOffPoleDecay
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleHorizontalEdgeBounds

/-!
# Zero-pole decay inputs

This file exposes the concrete decay inputs consumed by the zero-pole
vertical-orientation transport.

The theorems here are thin analytic wrappers over RH-lane owner theorems:
left off-pole decay and zero-pole horizontal decay.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The scheduled left zero-pole vertical trace tends to zero. -/
theorem completedZetaZeroPoleScheduledLeftVerticalTrace_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledLeftVerticalTraceFunction f F h)
      atTop
      (𝓝 0) :=
  zetaCompletedExplicitFormulaCorrectionLeftZeroPoleVerticalIntegral_tendsto_zero_ownerLeftOffPoleDecay
    f F h

/-- The scheduled zero-pole horizontal trace tends to zero. -/
theorem completedZetaZeroPoleScheduledHorizontalTrace_tendsto_zero
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledHorizontalTraceFunction f F h)
      atTop
      (𝓝 0) :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleScheduledHorizontalDifference_tendsto_zero_ownerZeroPoleHorizontal
    f F h

/--
The zero-pole right vertical trace follows from a tangent-boundary trace limit,
using the concrete left and horizontal decay inputs.
-/
theorem completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryTrace_and_decay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (B : ℂ)
    (htangent :
      Tendsto
        (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
        atTop
        (𝓝 B)) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-(B * Complex.I))) :=
  completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryTrace
    f F h B
    (completedZetaZeroPoleScheduledLeftVerticalTrace_tendsto_zero f F h)
    (completedZetaZeroPoleScheduledHorizontalTrace_tendsto_zero f F h)
    htangent

/--
Specialized right-vertical transport from a finite-square residue trace plus
orientation-defect tangent-boundary limit, using concrete decay inputs.
-/
theorem completedZetaZeroPoleRightVerticalTrace_tendsto_of_finiteSquareResidueTrace_orientationDefect_and_decay
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (D : ℂ)
    (htangent :
      Tendsto
        (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
        atTop
        (𝓝 (completedZetaZeroPoleFiniteSquareResidueTrace f + D))) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-((completedZetaZeroPoleFiniteSquareResidueTrace f + D) * Complex.I))) :=
  completedZetaZeroPoleRightVerticalTrace_tendsto_of_finiteSquareResidueTrace_and_orientationDefect
    f F h D
    (completedZetaZeroPoleScheduledLeftVerticalTrace_tendsto_zero f F h)
    (completedZetaZeroPoleScheduledHorizontalTrace_tendsto_zero f F h)
    htangent

end AnalyticMotives
end LFunctions
end Boundary
