import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pushforward.Components.Owner

/-!
# Motive-root pushforward naturality wrappers

This file mirrors compact-generator pushforward naturality under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root pushforward components commute with pullback along a probe. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_pullback_naturality
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
  TraceSixFunctorPushforward.compactGenerator_pullback_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
