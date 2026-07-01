import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.Adapters.CompletedZeta.FiniteRectangle.SoundnessSeed.ZeroPoleDecayInputs.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.ZeroPoleLaplaceProjection

/-!
# Zero-pole tangent-boundary convergence

This file exposes the concrete RH-lane theorem that the scheduled tangent
zero-pole boundary converges to the local tangent residue value, and identifies
that value with the finite-square residue trace used by the residue seed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The local tangent residue value agrees definitionally with the finite-square residue trace. -/
theorem completedZetaZeroPoleLocalTangentResidueValue_eq_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f =
      completedZetaZeroPoleFiniteSquareResidueTrace f :=
  rfl

/-- The scheduled tangent zero-pole boundary trace tends to the local tangent residue value. -/
theorem completedZetaZeroPoleScheduledTangentBoundaryTrace_tendsto_localTangentResidueValue
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaCorrectionZeroPoleLocalTangentResidueValue f)) :=
  zetaCompletedExplicitFormulaCorrectionZeroPoleTangentRectangleBoundaryIntegral_tendsto_localTangentResidueValue_ownerLaplaceProjection
    f F h

/-- The scheduled tangent zero-pole boundary trace tends to the finite-square residue trace. -/
theorem completedZetaZeroPoleScheduledTangentBoundaryTrace_tendsto_finiteSquareResidueTrace
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
      atTop
      (𝓝 (completedZetaZeroPoleFiniteSquareResidueTrace f)) :=
  Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (completedZetaZeroPoleScheduledTangentBoundaryTraceFunction f F h)
        atTop
        (𝓝 z))
    (completedZetaZeroPoleLocalTangentResidueValue_eq_finiteSquareResidueTrace f)
    (completedZetaZeroPoleScheduledTangentBoundaryTrace_tendsto_localTangentResidueValue
      f F h)

/-- The scheduled right vertical zero-pole trace tends to the tangent-transported residue value. -/
theorem completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryConvergence
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (completedZetaZeroPoleScheduledRightVerticalTraceFunction f F h)
      atTop
      (𝓝 (-(completedZetaZeroPoleFiniteSquareResidueTrace f * Complex.I))) :=
  completedZetaZeroPoleRightVerticalTrace_tendsto_of_tangentBoundaryTrace_and_decay
    f F h
    (completedZetaZeroPoleFiniteSquareResidueTrace f)
    (completedZetaZeroPoleScheduledTangentBoundaryTrace_tendsto_finiteSquareResidueTrace
      f F h)

end AnalyticMotives
end LFunctions
end Boundary
