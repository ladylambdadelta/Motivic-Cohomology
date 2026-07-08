import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Short complexes for fiber triangles

This owner file specializes the distinguished-triangle short-complex
construction to the chosen fiber triangle of a morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to the chosen fiber triangle of a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.fiberShortComplex
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory
    .shortComplexOfDistinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle_distinguished morphism)

/-- The first map of the chosen fiber short complex is the chosen fiber
map. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplex morphism).f =
      TraceAnalyticStableMotiveQuasicategory.fiberMap morphism :=
  rfl

/-- The second map of the chosen fiber short complex is the original
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplex morphism).g =
      morphism :=
  rfl

/-- The zero field of the chosen fiber short complex is the concrete
fiber-map zero-composition law. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplex morphism).zero =
      TraceAnalyticStableMotiveQuasicategory
        .fiberMap_comp_morphism morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
