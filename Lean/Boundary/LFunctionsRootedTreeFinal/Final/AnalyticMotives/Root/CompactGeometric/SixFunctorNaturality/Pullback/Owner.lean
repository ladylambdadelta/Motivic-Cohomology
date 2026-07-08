import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.CompactGeometric.SixFunctorNaturality.Pullback.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.CompactGeometric.SixFunctorNaturality.Pullback.Components.Owner

/-!
# Top-root pullback naturality wrappers

This file mirrors motive-root compact-generator pullback naturality under
`AnalyticMotivesRoot`.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root presheaf-morphism naturality for compact-generator pullback. -/
theorem AnalyticMotivesRoot.compactGeneratorPullback_naturality
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
  TraceAnalyticMotive.compactGeneratorPullback_naturality
    presheafMorphism
    traceMorphism

end AnalyticMotives
end LFunctions
end Boundary
