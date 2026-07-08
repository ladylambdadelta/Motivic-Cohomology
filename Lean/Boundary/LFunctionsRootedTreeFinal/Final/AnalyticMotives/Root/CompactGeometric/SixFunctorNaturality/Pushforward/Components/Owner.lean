import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pushforward.Components.Owner

/-!
# Top-root pushforward component wrappers

This file mirrors motive-root compact-generator pushforward component facts
under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root pushforward component is the representable-map component. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_eq_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      (TraceSixFunctorPushforward.compactGenerator morphism).component
        probe.traceObject :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_eq_component
    probe
    morphism

/-- Top-root evaluation of compact-generator pushforward gives its component. -/
theorem AnalyticMotivesRoot.evaluation_map_compactGeneratorPushforward
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.evaluation.map
        (TraceSixFunctorPushforward.compactGenerator morphism) =
      TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        morphism :=
  TraceAnalyticMotive.evaluation_map_compactGeneratorPushforward
    probe
    morphism

/-- Top-root pushforward component is the Yoneda component. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_eq_yoneda_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_eq_yoneda_component
    probe
    morphism

/-- Top-root identity pushforward component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_id
    probe
    generator

/-- Top-root composite pushforward component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGeneratorComponent probe left ≫
        TraceSixFunctorPushforward.compactGeneratorComponent probe right :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_comp
    probe
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
