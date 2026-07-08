import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Owner

/-!
# Pullback between compact-generator evaluations

This file records contravariant pullback on trace presheaf sections along a
compact-generator morphism.  It is exactly the existing trace-presheaf pullback
along the underlying trace correspondence.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Pull back sections along a compact-generator morphism. -/
def TraceAnalyticGeometricGenerator.pullback
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.sections presheaf ⟶ source.sections presheaf :=
  presheaf.pullback morphism.traceHom

/-- Compact-generator pullback is trace-presheaf pullback along the underlying trace hom. -/
theorem TraceAnalyticGeometricGenerator.pullback_eq_traceHom
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullback presheaf morphism =
      presheaf.pullback morphism.traceHom :=
  rfl

/-- Compact-generator pullback is functorial action on the opposite trace hom. -/
theorem TraceAnalyticGeometricGenerator.pullback_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullback presheaf morphism =
      presheaf.map morphism.traceHom.op :=
  TraceCorQPresheaf.pullback_eq_map_op presheaf morphism.traceHom

/-- Pullback along the identity compact-generator morphism is identity on sections. -/
theorem TraceAnalyticGeometricGenerator.pullback_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceCorQPresheaf.pullback_id presheaf generator.traceObject

/-- Compact-generator pullback is contravariantly functorial for composition. -/
theorem TraceAnalyticGeometricGenerator.pullback_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceAnalyticGeometricGenerator.pullback
        presheaf
        (left ≫ right) =
      TraceAnalyticGeometricGenerator.pullback presheaf right ≫
        TraceAnalyticGeometricGenerator.pullback presheaf left :=
  TraceCorQPresheaf.pullback_comp presheaf left.traceHom right.traceHom

/-- Presheaf morphism components commute with compact-generator pullback. -/
theorem TraceAnalyticGeometricGenerator.pullback_naturality
    {sourcePresheaf targetPresheaf : TraceCorQPresheaf}
    (presheafMorphism : sourcePresheaf ⟶ targetPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (traceMorphism : source ⟶ target) :
    TraceAnalyticGeometricGenerator.pullback
        sourcePresheaf
        traceMorphism ≫
        presheafMorphism.component source.traceObject =
      presheafMorphism.component target.traceObject ≫
        TraceAnalyticGeometricGenerator.pullback
          targetPresheaf
          traceMorphism :=
  TraceCorQPresheafHom.pullback_naturality
    presheafMorphism
    traceMorphism.traceHom

end AnalyticMotives
end LFunctions
end Boundary
