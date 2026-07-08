import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.SixFunctors.Pullback.Naturality.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pullback.Components.Owner

/-!
# Motive-root pullback naturality wrappers

This file mirrors compact-generator pullback naturality under
`TraceAnalyticMotive`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root presheaf-morphism naturality for compact-generator pullback. -/
theorem TraceAnalyticMotive.compactGeneratorPullback_naturality
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
  TraceSixFunctorPullback.compactGenerator_naturality
    presheafMorphism
    traceMorphism

end AnalyticMotives
end LFunctions
end Boundary
