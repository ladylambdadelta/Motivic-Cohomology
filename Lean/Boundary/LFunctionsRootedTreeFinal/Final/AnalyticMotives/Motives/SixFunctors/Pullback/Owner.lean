import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.CompactGeometric.Generators.Evaluation.Pullback.Owner

/-!
# Concrete compact-generator pullback functional

This file owns the first concrete six-functor functional currently available
in the analytic motives lane: contravariant pullback on compact-generator
evaluation sections along a compact-generator morphism.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The compact-generator pullback functional on trace-presheaf sections. -/
def TraceSixFunctorPullback.compactGenerator
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    target.sections presheaf ⟶ source.sections presheaf :=
  TraceAnalyticGeometricGenerator.pullback presheaf morphism

/-- Compact-generator six-functor pullback is the existing section pullback. -/
theorem TraceSixFunctorPullback.compactGenerator_eq
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGenerator presheaf morphism =
      TraceAnalyticGeometricGenerator.pullback presheaf morphism :=
  rfl

/-- Compact-generator six-functor pullback is trace-presheaf pullback along the trace hom. -/
theorem TraceSixFunctorPullback.compactGenerator_eq_traceHom
    (presheaf : TraceCorQPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (morphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGenerator presheaf morphism =
      presheaf.pullback morphism.traceHom :=
  TraceAnalyticGeometricGenerator.pullback_eq_traceHom
    presheaf
    morphism

/-- Compact-generator six-functor pullback is functorial for identities. -/
theorem TraceSixFunctorPullback.compactGenerator_id
    (presheaf : TraceCorQPresheaf)
    (generator : TraceAnalyticGeometricGenerator) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (𝟙 generator) =
      𝟙 (generator.sections presheaf) :=
  TraceAnalyticGeometricGenerator.pullback_id
    presheaf
    generator

/-- Compact-generator six-functor pullback is contravariantly functorial for composition. -/
theorem TraceSixFunctorPullback.compactGenerator_comp
    (presheaf : TraceCorQPresheaf)
    {first second third : TraceAnalyticGeometricGenerator}
    (left : first ⟶ second)
    (right : second ⟶ third) :
    TraceSixFunctorPullback.compactGenerator
        presheaf
        (left ≫ right) =
      TraceSixFunctorPullback.compactGenerator presheaf right ≫
        TraceSixFunctorPullback.compactGenerator presheaf left :=
  TraceAnalyticGeometricGenerator.pullback_comp
    presheaf
    left
    right

end AnalyticMotives
end LFunctions
end Boundary
