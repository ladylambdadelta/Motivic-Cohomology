import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Naturality.Owner

/-!
# Component interaction between pullback and pushforward

This file records the concrete Beck-Chevalley-shaped square available at the
current compact-generator level: pushforward components of representables
commute with pullback components along compact probe morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Pushforward components commute with pullback components along compact probe
morphisms.
-/
theorem TraceSixFunctorPullbackPushforward.compactGeneratorComponent_naturality
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    TraceSixFunctorPullback.compactGeneratorComponent
        source.presheaf
        probe ≫
        TraceSixFunctorPushforward.compactGeneratorComponent
          probeSource
          morphism =
      TraceSixFunctorPushforward.compactGeneratorComponent
          probeTarget
          morphism ≫
        TraceSixFunctorPullback.compactGeneratorComponent
          target.presheaf
          probe :=
  TraceSixFunctorPushforward.compactGenerator_pullback_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
