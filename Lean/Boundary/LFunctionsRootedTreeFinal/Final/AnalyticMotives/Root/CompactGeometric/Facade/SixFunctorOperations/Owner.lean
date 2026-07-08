import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorNaturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorRepresentable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.Facade.PullbackEvaluationPayload.Owner

/-!
# Top-root compact-geometric six-functor operation facade
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes compact-generator pullback identities. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceAnalyticMotive.compactGeneratorPullback_id
    presheaf
    generator

/-- The analytic-motives root exposes compact-generator pullback composition. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGenerator presheaf right ≫
        TraceSixFunctorPullback.compactGenerator presheaf left :=
  TraceAnalyticMotive.compactGeneratorPullback_comp
    presheaf
    left
    right

/-- The analytic-motives root exposes compact-generator pushforward identities. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_id
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGenerator
        (𝟙 generator) =
      𝟙 generator.presheaf :=
  TraceAnalyticMotive.compactGeneratorPushforward_id
    generator

/-- The analytic-motives root exposes compact-generator pushforward composition. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforward_comp
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGenerator
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGenerator left ≫
        TraceSixFunctorPushforward.compactGenerator right :=
  TraceAnalyticMotive.compactGeneratorPushforward_comp
    left
    right

/-- The analytic-motives root exposes representable pullback-pushforward naturality. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackPushforward_representable_naturality
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
  TraceAnalyticMotive.compactGeneratorPullbackPushforward_representable_naturality
    morphism
    probe

end AnalyticMotives
end LFunctions
end Boundary
