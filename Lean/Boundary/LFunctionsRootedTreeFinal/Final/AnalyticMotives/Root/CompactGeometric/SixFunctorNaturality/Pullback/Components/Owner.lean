import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pullback.Components.Owner

/-!
# Top-root pullback component wrappers

This file mirrors motive-root compact-generator pullback component facts under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root pullback component is compact-generator pullback. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_eq_compactGenerator
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      TraceSixFunctorPullback.compactGenerator presheaf morphism :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_compactGenerator
    presheaf
    morphism

/-- Top-root pullback component is trace-hom pullback. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_eq_traceHom
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.pullback morphism.traceHom :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_traceHom
    presheaf
    morphism

/-- Top-root pullback component is opposite trace-hom functorial action. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.map morphism.traceHom.op :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_map_op
    presheaf
    morphism

/-- Top-root identity pullback component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_id
    presheaf
    generator

/-- Top-root composite pullback component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGeneratorComponent presheaf right ≫
        TraceSixFunctorPullback.compactGeneratorComponent presheaf left :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_comp
    presheaf
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
