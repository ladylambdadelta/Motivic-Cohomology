import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pushforward.Components.Owner

/-!
# Pushforward on representable compact generators

This file records that compact-generator pushforward on representable
presheaves is the concrete postcomposition operator on trace correspondences.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete postcomposition operator on trace hom modules. -/
def TraceSixFunctorPushforward.representablePostcompositionOperator
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    ModuleCat.of Rat (probe.traceObject ⟶ source.traceObject) ⟶
      ModuleCat.of Rat (probe.traceObject ⟶ target.traceObject) :=
  ModuleCat.asHom
    (CategoryTheory.Linear.rightComp
      Rat
      probe.traceObject
      morphism.traceHom)

/-- The source module of representable postcomposition is the probe-to-source trace hom module. -/
theorem TraceSixFunctorPushforward.representablePostcompositionOperator_sourceModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections source.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ source.traceObject) :=
  TraceAnalyticGeometricGenerator.representable_sections
    probe
    source

/-- The target module of representable postcomposition is the probe-to-target trace hom module. -/
theorem TraceSixFunctorPushforward.representablePostcompositionOperator_targetModule
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    probe.sections target.presheaf =
      ModuleCat.of Rat (probe.traceObject ⟶ target.traceObject) :=
  TraceAnalyticGeometricGenerator.representable_sections
    probe
    target

/-- Pushforward of a representable compact generator is postcomposition by the trace hom. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_representable
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        morphism :=
  rfl

/-- The named postcomposition operator unfolds to `Linear.rightComp`. -/
theorem TraceSixFunctorPushforward.representablePostcompositionOperator_eq_rightComp
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
  rfl

/-- The representable postcomposition operator sends identity to identity. -/
theorem TraceSixFunctorPushforward.representablePostcompositionOperator_id
    (probe generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (𝟙 generator) =
      𝟙 (probe.sections generator.presheaf) :=
  Eq.trans
    (Eq.symm
      (TraceSixFunctorPushforward.compactGeneratorComponent_representable
        probe
        (𝟙 generator)))
    (TraceSixFunctorPushforward.compactGeneratorComponent_id
      probe
      generator)

/-- The representable postcomposition operator is covariantly functorial. -/
theorem TraceSixFunctorPushforward.representablePostcompositionOperator_comp
    (probe : TraceAnalyticGeometricGenerator)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPushforward.representablePostcompositionOperator
        probe
        (left ≫ right) =
      TraceSixFunctorPushforward.representablePostcompositionOperator probe left ≫
        TraceSixFunctorPushforward.representablePostcompositionOperator probe right :=
  Eq.trans
    (Eq.symm
      (TraceSixFunctorPushforward.compactGeneratorComponent_representable
        probe
        (left ≫ right)))
    (Eq.trans
      (TraceSixFunctorPushforward.compactGeneratorComponent_comp
        probe
        left
        right)
      (congrArg₂
        (fun firstMap secondMap => firstMap ≫ secondMap)
        (TraceSixFunctorPushforward.compactGeneratorComponent_representable
          probe
          left)
        (TraceSixFunctorPushforward.compactGeneratorComponent_representable
          probe
          right)))

/-- Compact-generator pushforward on representables is the component of the Yoneda map. -/
theorem TraceSixFunctorPushforward.compactGeneratorComponent_representable_eq_yoneda
    (probe : TraceAnalyticGeometricGenerator)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPushforward.compactGeneratorComponent probe morphism =
      ((TraceCorQPresheaf.yoneda).map morphism.traceHom).app
        (Opposite.op probe.traceObject) :=
  TraceSixFunctorPushforward.compactGeneratorComponent_eq_yoneda_component
    probe
    morphism

end AnalyticMotives
end LFunctions
end Boundary
