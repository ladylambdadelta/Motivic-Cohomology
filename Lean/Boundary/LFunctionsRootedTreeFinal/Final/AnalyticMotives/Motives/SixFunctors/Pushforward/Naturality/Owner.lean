import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Owner

/-!
# Naturality for compact-generator pushforward

This file records that compact-generator pushforward, as a morphism of
representable trace presheaves, commutes with compact-generator pullback along
probe morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Compact-generator pushforward components commute with compact-generator
pullback along a probe morphism.
-/
theorem TraceSixFunctorPushforward.compactGenerator_pullback_naturality
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.compactGenerator
        source.presheaf
        probe ≫
        (TraceSixFunctorPushforward.compactGenerator morphism).component
          probeSource.traceObject =
      (TraceSixFunctorPushforward.compactGenerator morphism).component
          probeTarget.traceObject ≫
        TraceSixFunctorPullback.compactGenerator
          target.presheaf
          probe :=
  TraceSixFunctorPullback.compactGenerator_naturality
    (TraceSixFunctorPushforward.compactGenerator morphism)
    probe

end AnalyticMotives
end LFunctions
end Boundary
