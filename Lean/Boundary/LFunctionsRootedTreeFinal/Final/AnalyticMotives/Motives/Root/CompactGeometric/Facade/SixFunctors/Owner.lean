import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.Facade.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorRepresentable.Owner

/-!
# Motive-root compact-geometric six-functor facade

This file exposes compact-generator pullback, pushforward, and representable
naturality laws under the `TraceAnalyticMotive` root facade.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Compact-generator pullback is identity-functorial. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceSixFunctor.compactGeneratorPullback_id
    presheaf
    generator

/-- Compact-generator pullback is contravariantly compositional. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGenerator presheaf right ≫
        TraceSixFunctorPullback.compactGenerator presheaf left :=
  TraceSixFunctor.compactGeneratorPullback_comp
    presheaf
    left
    right

/-- Compact-generator pushforward is identity-functorial. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGenerator
        (𝟙 generator) =
      𝟙 generator.presheaf :=
  TraceSixFunctor.compactGeneratorPushforward_id
    generator

/-- Compact-generator pushforward is covariantly compositional. -/
theorem TraceAnalyticMotive.compactGeneratorPushforward_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGenerator
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGenerator left ≫
        TraceSixFunctorPushforward.compactGenerator right :=
  TraceSixFunctor.compactGeneratorPushforward_comp
    left
    right

/-- Compact-generator representable pullback and pushforward commute. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackPushforward_representable_naturality
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
  TraceSixFunctor.compactGeneratorPullbackPushforward_representable_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
