import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Interaction.PullbackPushforward.Components.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Representable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Representable.Owner

/-!
# Representable interaction between pullback and pushforward

This file records the compact-generator pullback-pushforward square in the
concrete hom-module presentation: pullback is precomposition and pushforward is
postcomposition.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
On representable compact generators, precomposition by a probe morphism
commutes with postcomposition by a target morphism.
-/
theorem TraceSixFunctorPullbackPushforward.representable_leftComp_rightComp_naturality
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target)
    {probeSource probeTarget : TraceAnalyticGeometricGenerator}
    (probe : probeSource ⟶ probeTarget) :
    ModuleCat.asHom
        (CategoryTheory.Linear.leftComp
          Rat
          source.traceObject
          probe.traceHom) ≫
        ModuleCat.asHom
          (CategoryTheory.Linear.rightComp
            Rat
            probeSource.traceObject
            morphism.traceHom) =
      ModuleCat.asHom
          (CategoryTheory.Linear.rightComp
            Rat
            probeTarget.traceObject
            morphism.traceHom) ≫
        ModuleCat.asHom
          (CategoryTheory.Linear.leftComp
            Rat
            target.traceObject
            probe.traceHom) :=
  TraceSixFunctorPullbackPushforward.compactGeneratorComponent_naturality
    morphism
    probe

/--
The named representable precomposition and postcomposition operators commute in
the compact pullback-pushforward square.
-/
theorem TraceSixFunctorPullbackPushforward.representableOperator_naturality
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
  TraceSixFunctorPullbackPushforward.representable_leftComp_rightComp_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
