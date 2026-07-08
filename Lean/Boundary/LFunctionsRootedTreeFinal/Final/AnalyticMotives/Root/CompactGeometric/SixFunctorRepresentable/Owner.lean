import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorRepresentable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorRepresentable.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorRepresentable.Pushforward.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorRepresentable.Pushforward.Yoneda.Owner

/-!
# Top-root representable six-functor wrappers

This file collects top-root facades for representable compact-generator
pullback and pushforward operators.  The aggregate surface records the three
basic representable identifications: pullback is left composition, pushforward
is right composition, and lifted pushforward is recovered by Yoneda preimage.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root representable pullback is trace-hom left composition. -/
theorem AnalyticMotivesRoot.representableSixFunctor_pullback_eq_leftComp
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        morphism =
      ModuleCat.asHom
        (CategoryTheory.Linear.leftComp
          Rat
          target.traceObject
          morphism.traceHom) :=
  TraceAnalyticMotive.representableSixFunctor_pullback_eq_leftComp
    target
    morphism

/-- Top-root representable pushforward is trace-hom right composition. -/
theorem AnalyticMotivesRoot.representableSixFunctor_pushforward_eq_rightComp
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        morphism =
      ModuleCat.asHom
        (CategoryTheory.Linear.rightComp
          Rat
          probe.traceObject
          morphism.traceHom) :=
  TraceAnalyticMotive.representableSixFunctor_pushforward_eq_rightComp
    probe
    morphism

/-- Top-root lifted representable pushforward has the compact morphism as Yoneda preimage. -/
theorem AnalyticMotivesRoot.representableSixFunctor_pushforward_yonedaPreimage
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.yonedaPreimage
        (TraceSixFunctorPushforward.compactGeneratorObject morphism) =
      morphism :=
  TraceAnalyticMotive.representableSixFunctor_pushforward_yonedaPreimage
    morphism

end AnalyticMotives
end LFunctions
end Boundary
