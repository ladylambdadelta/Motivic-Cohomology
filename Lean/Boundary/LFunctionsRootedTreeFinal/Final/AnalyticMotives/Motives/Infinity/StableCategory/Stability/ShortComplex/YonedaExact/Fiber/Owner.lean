import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner

/-!
# Yoneda exactness for fiber short complexes

This owner file specializes Yoneda exactness to the chosen fiber triangle of
a morphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Covariant preadditive Yoneda exactness for the chosen fiber triangle of a
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .fiberTriangle_distinguished morphism)
      probe

/-- Contravariant preadditive Yoneda exactness for the chosen fiber triangle
of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .fiberTriangle_distinguished morphism)
      probe

end AnalyticMotives
end LFunctions
end Boundary
