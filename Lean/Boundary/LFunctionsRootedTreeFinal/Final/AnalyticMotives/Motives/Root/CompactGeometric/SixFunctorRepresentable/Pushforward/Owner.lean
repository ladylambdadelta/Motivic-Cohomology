import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Representable.Owner

/-!
# Motive-root representable pushforward wrappers

This file mirrors the representable compact-generator pushforward operator
facts under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root representable postcomposition source module wrapper. -/
theorem TraceAnalyticMotive.representablePostcompositionOperator_sourceModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections source.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ source.traceObject) :=
  TraceSixFunctorPushforward.representablePostcompositionOperator_sourceModule
    probe
    morphism

/-- Motive-root representable postcomposition target module wrapper. -/
theorem TraceAnalyticMotive.representablePostcompositionOperator_targetModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections target.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ target.traceObject) :=
  TraceSixFunctorPushforward.representablePostcompositionOperator_targetModule
    probe
    morphism

/-- Motive-root representable pushforward component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_representable
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        morphism :=
  TraceSixFunctorPushforward.compactGeneratorComponent_representable
    probe
    morphism

/-- Motive-root representable postcomposition unfolds to right composition. -/
theorem TraceAnalyticMotive.representablePostcompositionOperator_eq_rightComp
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
  TraceSixFunctorPushforward.representablePostcompositionOperator_eq_rightComp
    probe
    morphism

/-- Motive-root representable postcomposition sends identity to identity. -/
theorem TraceAnalyticMotive.representablePostcompositionOperator_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  TraceSixFunctorPushforward.representablePostcompositionOperator_id
    probe
    generator

/-- Motive-root representable postcomposition is covariantly functorial. -/
theorem TraceAnalyticMotive.representablePostcompositionOperator_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.representablePostcompositionOperator probe left ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator probe right :=
  TraceSixFunctorPushforward.representablePostcompositionOperator_comp
    probe
    left
    right

/-- Motive-root representable pushforward is the Yoneda component. -/
theorem TraceAnalyticMotive.compactGeneratorPushforwardComponent_representable_eq_yoneda
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_representable_eq_yoneda
    probe
    morphism

end AnalyticMotives
end LFunctions
end Boundary
