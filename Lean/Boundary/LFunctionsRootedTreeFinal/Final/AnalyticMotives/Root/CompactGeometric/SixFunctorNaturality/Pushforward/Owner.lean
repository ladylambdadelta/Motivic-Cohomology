import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorNaturality.Pushforward.Components.Owner

/-!
# Top-root pushforward naturality wrappers

This file mirrors motive-root compact-generator pushforward naturality under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root pushforward components commute with pullback along a probe. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_pullback_naturality
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
  TraceAnalyticMotive.compactGeneratorPushforward_pullback_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
