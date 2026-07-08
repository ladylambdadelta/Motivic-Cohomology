import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Representable.Owner

/-!
# Motive-root representable pullback wrappers

This file mirrors the representable compact-generator pullback operator facts
under `TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root representable precomposition source module wrapper. -/
theorem TraceAnalyticMotive.representablePrecompositionOperator_sourceModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    middle.sections target.presheaf =
      ModuleCat.of Rat (middle.traceObject ⟶ target.traceObject) :=
  TraceSixFunctorPullback.representablePrecompositionOperator_sourceModule
    target
    morphism

/-- Motive-root representable precomposition target module wrapper. -/
theorem TraceAnalyticMotive.representablePrecompositionOperator_targetModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceSixFunctorPullback.representablePrecompositionOperator_targetModule
    target
    morphism

/-- Motive-root representable pullback component wrapper. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_representable
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      TraceSixFunctorPullback.representablePrecompositionOperator
        target
        morphism :=
  TraceSixFunctorPullback.compactGeneratorComponent_representable
    target
    morphism

/-- Motive-root representable precomposition unfolds to left composition. -/
theorem TraceAnalyticMotive.representablePrecompositionOperator_eq_leftComp
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
  TraceSixFunctorPullback.representablePrecompositionOperator_eq_leftComp
    target
    morphism

/-- Motive-root representable precomposition sends identity to identity. -/
theorem TraceAnalyticMotive.representablePrecompositionOperator_id
    (target generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (𝟙 generator) =
      𝟙 (generator.sections target.presheaf) :=
  TraceSixFunctorPullback.representablePrecompositionOperator_id
    target
    generator

/-- Motive-root representable precomposition is contravariantly functorial. -/
theorem TraceAnalyticMotive.representablePrecompositionOperator_comp
    (target : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (left ≫ right) =
      TraceSixFunctorPullback.representablePrecompositionOperator target right ≫
        TraceSixFunctorPullback.representablePrecompositionOperator target left :=
  TraceSixFunctorPullback.representablePrecompositionOperator_comp
    target
    left
    right

/-- Motive-root representable pullback agrees with presheaf representable pullback. -/
theorem TraceAnalyticMotive.compactGeneratorPullbackComponent_representable_eq_presheaf
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      (TraceCorQPresheaf.representable
        target.traceObject).pullback morphism.traceHom :=
  TraceSixFunctorPullback.compactGeneratorComponent_representable_eq_presheaf
    target
    morphism

end AnalyticMotives
end LFunctions
end Boundary
