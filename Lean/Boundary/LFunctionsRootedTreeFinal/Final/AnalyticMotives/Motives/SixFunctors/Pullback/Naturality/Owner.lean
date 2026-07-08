import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Owner

/-!
# Naturality for compact-generator pullback

This file records naturality of the concrete compact-generator pullback
functional with respect to trace-presheaf morphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Presheaf morphism components commute with compact-generator six-functor pullback. -/
theorem TraceSixFunctorPullback.compactGenerator_naturality
    {sourcePresheaf targetPresheaf : TraceCorQPresheaf}
    (presheafMorphism : sourcePresheaf ⟶ targetPresheaf)
    {source target : TraceAnalyticGeometricGenerator}
    (traceMorphism : source ⟶ target) :
    TraceSixFunctorPullback.compactGenerator
        sourcePresheaf
        traceMorphism ≫
        presheafMorphism.component source.traceObject =
      presheafMorphism.component target.traceObject ≫
        TraceSixFunctorPullback.compactGenerator
          targetPresheaf
          traceMorphism :=
  TraceAnalyticGeometricGenerator.pullback_naturality
    presheafMorphism
    traceMorphism

end AnalyticMotives
end LFunctions
end Boundary
