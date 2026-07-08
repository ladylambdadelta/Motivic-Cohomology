import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Owner

/-!
# Section components of compact-generator pushforward

This file records the concrete maps on sections obtained by evaluating
compact-generator pushforward at a compact probe generator.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The section map of compact-generator pushforward at a compact probe. -/
def TraceSixFunctorPushforward.compactGeneratorComponent
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections source.presheaf ⟶ probe.sections target.presheaf :=
  (TraceSixFunctorPushforward.compactGenerator morphism).component
    probe.traceObject

/-- The pushforward component is the component of the representable map. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_eq_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      (TraceSixFunctorPushforward.compactGenerator morphism).component
        probe.traceObject :=
  rfl

/-- Evaluating compact-generator pushforward at a probe gives its section component. -/
theorem TraceSixFunctorPushforward.evaluation_map_compactGenerator
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.evaluation.map
        (TraceSixFunctorPushforward.compactGenerator morphism) =
      TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        morphism :=
  rfl

/-- The pushforward component is the linear-Yoneda component of the trace hom. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_eq_yoneda_component
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceCorQPresheaf.representableMap_component
    morphism.traceHom
    probe.traceObject

/-- Identity pushforward has identity section component at every compact probe. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  congrArg
    (fun map =>
      TraceCorQPresheafHom.component map probe.traceObject)
    (TraceSixFunctorPushforward.compactGenerator_id generator)

/-- Composite pushforward components compose covariantly at every compact probe. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.compactGeneratorComponent
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.compactGeneratorComponent probe left ≫
        TraceSixFunctorPushforward.compactGeneratorComponent probe right :=
  congrArg
    (fun map =>
      TraceCorQPresheafHom.component map probe.traceObject)
    (TraceSixFunctorPushforward.compactGenerator_comp left right)

end AnalyticMotives
end LFunctions
end Boundary
