import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.Operations.Owner

/-!
# Interactions between six-functor components

This directory owns concrete interaction laws between the compact-generator
six-functor operations currently constructed in the analytic motives lane.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-generator pullback and pushforward commute on representable operators. -/
theorem TraceSixFunctorInteraction.pullbackPushforward_representable_naturality
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        source
        probe ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator
          probeSource
          morphism =
      TraceSixFunctorPushforward.representablePostcompositionOperator
          probeTarget
          morphism ≫
        TraceSixFunctorPullback.representablePrecompositionOperator
          target
          probe :=
  TraceSixFunctorPullbackPushforward.representableOperator_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
