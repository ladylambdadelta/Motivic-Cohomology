import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Components.Owner

/-!
# Motive-root pushforward component wrappers

This file mirrors compact-generator pushforward component facts under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root pushforward component is the representable-map component. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_eq_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      (TraceSixFunctorPushforward.compactGenerator morphism).component
        probe.traceObject :=
  TraceSixFunctorPushforward.compactGeneratorComponent_eq_component
    probe
    morphism

/-- Motive-root evaluation of compact-generator pushforward gives its component. -/
theorem TraceAnalyticMotive.evaluation_map_compactGeneratorPushforward
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.evaluation.map
        (TraceSixFunctorPushforward.compactGenerator morphism) =
      TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        morphism :=
  TraceSixFunctorPushforward.evaluation_map_compactGenerator
    probe
    morphism

/-- Motive-root pushforward component is the Yoneda component. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_eq_yoneda_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_eq_yoneda_component
    probe
    morphism

/-- Motive-root identity pushforward component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_id
    probe
    generator

/-- Motive-root composite pushforward component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGeneratorComponent probe left ≫
        TraceSixFunctorPushforward.compactGeneratorComponent probe right :=
  TraceSixFunctorPushforward.compactGeneratorComponent_comp
    probe
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
