import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorRepresentable.Pushforward.Owner

/-!
# Top-root representable pushforward wrappers

This file mirrors the motive-root representable compact-generator pushforward
operator facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root representable postcomposition source module wrapper. -/
theorem AnalyticMotivesRoot.representablePostcompositionOperator_sourceModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections source.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ source.traceObject) :=
  TraceAnalyticMotive.representablePostcompositionOperator_sourceModule
    probe
    morphism

/-- Top-root representable postcomposition target module wrapper. -/
theorem AnalyticMotivesRoot.representablePostcompositionOperator_targetModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections target.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.representablePostcompositionOperator_targetModule
    probe
    morphism

/-- Top-root representable pushforward component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_representable
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        morphism :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_representable
    probe
    morphism

/-- Top-root representable postcomposition unfolds to right composition. -/
theorem AnalyticMotivesRoot.representablePostcompositionOperator_eq_rightComp
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
  TraceAnalyticMotive.representablePostcompositionOperator_eq_rightComp
    probe
    morphism

/-- Top-root representable postcomposition sends identity to identity. -/
theorem AnalyticMotivesRoot.representablePostcompositionOperator_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  TraceAnalyticMotive.representablePostcompositionOperator_id
    probe
    generator

/-- Top-root representable postcomposition is covariantly functorial. -/
theorem AnalyticMotivesRoot.representablePostcompositionOperator_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.representablePostcompositionOperator probe left ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator probe right :=
  TraceAnalyticMotive.representablePostcompositionOperator_comp
    probe
    left
    right

/-- Top-root representable pushforward is the Yoneda component. -/
theorem AnalyticMotivesRoot.compactGeneratorPushforwardComponent_representable_eq_yoneda
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceAnalyticMotive.compactGeneratorPushforwardComponent_representable_eq_yoneda
    probe
    morphism

end AnalyticMotives
end LFunctions
end Boundary
