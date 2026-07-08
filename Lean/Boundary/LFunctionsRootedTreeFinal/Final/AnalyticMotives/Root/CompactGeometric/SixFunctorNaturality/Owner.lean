import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorNaturality.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorNaturality.Pushforward.Owner

/-!
# Top-root six-functor component and naturality wrappers

This file collects top-root facades for compact-generator pullback and
pushforward component and naturality facts.  The aggregate surface records the
two concrete naturality squares used by the representable calculus.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root aggregate pullback naturality against a presheaf morphism. -/
theorem AnalyticMotivesRoot.sixFunctorNaturality_pullback
    {sourcePresheaf targetPresheaf : TraceCorQPresheaf}
    (presheafMorphism : sourcePresheaf ⟶ targetPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (traceMorphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGenerator
        sourcePresheaf
        traceMorphism ≫
        presheafMorphism.component source.traceObject =
      presheafMorphism.component target.traceObject ≫
        TraceSixFunctorPullback.compactGenerator
          targetPresheaf
          traceMorphism :=
  TraceAnalyticMotive.sixFunctorNaturality_pullback
    presheafMorphism
    traceMorphism

/-- Top-root aggregate pushforward components commute with pullback along a probe. -/
theorem AnalyticMotivesRoot.sixFunctorNaturality_pushforward_pullback
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
  TraceAnalyticMotive.sixFunctorNaturality_pushforward_pullback
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
