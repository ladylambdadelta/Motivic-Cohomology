import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorRepresentable.Pullback.Owner

/-!
# Top-root representable pullback wrappers

This file mirrors the motive-root representable compact-generator pullback
operator facts under `AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root representable precomposition source module wrapper. -/
theorem AnalyticMotivesRoot.representablePrecompositionOperator_sourceModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    middle.sections target.presheaf =
      ModuleCat.of Rat (middle.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.representablePrecompositionOperator_sourceModule
    target
    morphism

/-- Top-root representable precomposition target module wrapper. -/
theorem AnalyticMotivesRoot.representablePrecompositionOperator_targetModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticMotive.representablePrecompositionOperator_targetModule
    target
    morphism

/-- Top-root representable pullback component wrapper. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_representable
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      TraceSixFunctorPullback.representablePrecompositionOperator
        target
        morphism :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_representable
    target
    morphism

/-- Top-root representable precomposition unfolds to left composition. -/
theorem AnalyticMotivesRoot.representablePrecompositionOperator_eq_leftComp
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        morphism =
      ModuleCat.asHom
        (CategoryTheory.Linear.leftComp
          Rat
          target.traceObject
          morphism.traceHom) :=
  TraceAnalyticMotive.representablePrecompositionOperator_eq_leftComp
    target
    morphism

/-- Top-root representable precomposition sends identity to identity. -/
theorem AnalyticMotivesRoot.representablePrecompositionOperator_id
    (target generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (𝟙 generator) =
      𝟙 (generator.sections target.presheaf) :=
  TraceAnalyticMotive.representablePrecompositionOperator_id
    target
    generator

/-- Top-root representable precomposition is contravariantly functorial. -/
theorem AnalyticMotivesRoot.representablePrecompositionOperator_comp
    (target : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (left ≫ right) =
      TraceSixFunctorPullback.representablePrecompositionOperator target right ≫
        TraceSixFunctorPullback.representablePrecompositionOperator target left :=
  TraceAnalyticMotive.representablePrecompositionOperator_comp
    target
    left
    right

/-- Top-root representable pullback agrees with presheaf representable pullback. -/
theorem AnalyticMotivesRoot.compactGeneratorPullbackComponent_representable_eq_presheaf
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      (TraceCorQPresheaf.representable
        target.traceObject).pullback morphism.traceHom :=
  TraceAnalyticMotive.compactGeneratorPullbackComponent_representable_eq_presheaf
    target
    morphism

end AnalyticMotives
end LFunctions
end Boundary
