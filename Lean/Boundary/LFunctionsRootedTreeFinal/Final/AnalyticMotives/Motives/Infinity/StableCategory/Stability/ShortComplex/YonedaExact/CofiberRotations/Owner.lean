import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.CofiberRotations.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.YonedaExact.Owner

/-!
# Yoneda exactness for rotated cofiber short complexes

This owner file specializes Yoneda exactness to the rotated and
inverse-rotated chosen cofiber triangles of analytic stable motives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Covariant preadditive Yoneda exactness for the rotated chosen cofiber
triangle of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberTriangle_distinguished morphism)
      probe

/-- Contravariant preadditive Yoneda exactness for the rotated chosen cofiber
triangle of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .rotatedCofiberTriangle_distinguished morphism)
      probe

/-- Covariant preadditive Yoneda exactness for the inverse-rotated chosen
cofiber triangle of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle_distinguished morphism)
      probe

/-- Contravariant preadditive Yoneda exactness for the inverse-rotated chosen
cofiber triangle of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle_distinguished morphism)
      probe

end AnalyticMotives
end LFunctions
end Boundary
