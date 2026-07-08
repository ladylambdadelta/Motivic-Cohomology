import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Components.Owner

/-!
# Pullback on representable compact generators

This file records that compact-generator pullback on a representable presheaf
is the concrete precomposition operator on trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete precomposition operator on trace hom modules. -/
def TraceSixFunctorPullback.representablePrecompositionOperator
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    ModuleCat.of Rat (middle.traceObject ⟶ target.traceObject) ⟶
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  ModuleCat.asHom
    (CategoryTheory.Linear.leftComp
      Rat
      target.traceObject
      morphism.traceHom)

/-- The source module of representable precomposition is the middle-to-target trace hom module. -/
theorem TraceSixFunctorPullback.representablePrecompositionOperator_sourceModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    middle.sections target.presheaf =
      ModuleCat.of Rat (middle.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.representable_sections
    middle
    target

/-- The target module of representable precomposition is the source-to-target trace hom module. -/
theorem TraceSixFunctorPullback.representablePrecompositionOperator_targetModule
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    source.sections target.presheaf =
      ModuleCat.of Rat (source.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.representable_sections
    source
    target

/-- Pullback of a representable compact generator is precomposition by the trace hom. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_representable
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      TraceSixFunctorPullback.representablePrecompositionOperator
        target
        morphism :=
  TraceCorQPresheaf.representable_pullback
    target.traceObject
    morphism.traceHom

/-- The named precomposition operator unfolds to `Linear.leftComp`. -/
theorem TraceSixFunctorPullback.representablePrecompositionOperator_eq_leftComp
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
  rfl

/-- The representable precomposition operator sends identity to identity. -/
theorem TraceSixFunctorPullback.representablePrecompositionOperator_id
    (target generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (𝟙 generator) =
      𝟙 (generator.sections target.presheaf) :=
  Eq.trans
    (Eq.symm
      (TraceSixFunctorPullback.compactGeneratorComponent_representable
        target
        (𝟙 generator)))
    (TraceSixFunctorPullback.compactGeneratorComponent_id
      target.presheaf
      generator)

/-- The representable precomposition operator is contravariantly functorial. -/
theorem TraceSixFunctorPullback.representablePrecompositionOperator_comp
    (target : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.representablePrecompositionOperator
        target
        (left ≫ right) =
      TraceSixFunctorPullback.representablePrecompositionOperator target right ≫
        TraceSixFunctorPullback.representablePrecompositionOperator target left :=
  Eq.trans
    (Eq.symm
      (TraceSixFunctorPullback.compactGeneratorComponent_representable
        target
        (left ≫ right)))
    (Eq.trans
      (TraceSixFunctorPullback.compactGeneratorComponent_comp
        target.presheaf
        left
        right)
      (congrArg₂
        (fun firstMap secondMap => firstMap ≫ secondMap)
        (TraceSixFunctorPullback.compactGeneratorComponent_representable
          target
          right)
        (TraceSixFunctorPullback.compactGeneratorComponent_representable
          target
          left)))

/-- Compact-generator pullback on representables agrees with trace-presheaf representable pullback. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_representable_eq_presheaf
    {source middle : TraceAnalyticGeometricGenerator}
    (target : TraceAnalyticGeometricGenerator)
    (morphism : source ⟶ middle) :
    TraceSixFunctorPullback.compactGeneratorComponent
        target.presheaf
        morphism =
      (TraceCorQPresheaf.representable
        target.traceObject).pullback morphism.traceHom :=
  TraceSixFunctorPullback.compactGeneratorComponent_eq_traceHom
    target.presheaf
    morphism

end AnalyticMotives
end LFunctions
end Boundary
