import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Components.Owner

/-!
# Motive-root pullback component wrappers

This file mirrors compact-generator pullback component facts under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root pullback component is compact-generator pullback. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_compactGenerator
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      TraceSixFunctorPullback.compactGenerator presheaf morphism :=
  TraceSixFunctorPullback.compactGeneratorComponent_eq_compactGenerator
    presheaf
    morphism

/-- Motive-root pullback component is trace-hom pullback. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_traceHom
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.pullback morphism.traceHom :=
  TraceSixFunctorPullback.compactGeneratorComponent_eq_traceHom
    presheaf
    morphism

/-- Motive-root pullback component is opposite trace-hom functorial action. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.map morphism.traceHom.op :=
  TraceSixFunctorPullback.compactGeneratorComponent_eq_map_op
    presheaf
    morphism

/-- Motive-root identity pullback component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceSixFunctorPullback.compactGeneratorComponent_id
    presheaf
    generator

/-- Motive-root composite pullback component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGeneratorComponent presheaf right ≫
        TraceSixFunctorPullback.compactGeneratorComponent presheaf left :=
  TraceSixFunctorPullback.compactGeneratorComponent_comp
    presheaf
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
