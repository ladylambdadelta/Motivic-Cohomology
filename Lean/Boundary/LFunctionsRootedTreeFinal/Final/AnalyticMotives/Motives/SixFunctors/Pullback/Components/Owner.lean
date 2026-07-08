import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Owner

/-!
# Section components of compact-generator pullback

This file records the concrete section maps obtained from compact-generator
pullback on a fixed trace presheaf.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The section map of compact-generator pullback for a fixed presheaf. -/
def TraceSixFunctorPullback.compactGeneratorComponent
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.sections presheaf ⟶ source.sections presheaf :=
  TraceSixFunctorPullback.compactGenerator presheaf morphism

/-- The pullback component is the compact-generator pullback map. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_eq_compactGenerator
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      TraceSixFunctorPullback.compactGenerator presheaf morphism :=
  rfl

/-- The pullback component is the trace-presheaf pullback along the underlying trace hom. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_eq_traceHom
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.pullback morphism.traceHom :=
  TraceSixFunctorPullback.compactGenerator_eq_traceHom
    presheaf
    morphism

/-- The pullback component is functorial action on the opposite trace hom. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_eq_map_op
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGeneratorComponent presheaf morphism =
      presheaf.map morphism.traceHom.op :=
  TraceAnalyticGeometricGenerator.pullback_eq_map_op
    presheaf
    morphism

/-- Identity pullback has identity section component for every presheaf. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceSixFunctorPullback.compactGenerator_id
    presheaf
    generator

/-- Composite pullback components compose contravariantly for every presheaf. -/
theorem TraceSixFunctorPullback.compactGeneratorComponent_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGeneratorComponent
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGeneratorComponent presheaf right ≫
        TraceSixFunctorPullback.compactGeneratorComponent presheaf left :=
  TraceSixFunctorPullback.compactGenerator_comp
    presheaf
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
