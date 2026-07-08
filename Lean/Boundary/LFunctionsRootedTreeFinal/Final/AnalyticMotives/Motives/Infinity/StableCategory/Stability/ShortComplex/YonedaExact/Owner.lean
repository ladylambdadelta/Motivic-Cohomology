import Mathlib.CategoryTheory.Triangulated.Yoneda
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Yoneda exactness for analytic stable motive triangles

This owner file records the exactness supplied by homological Yoneda probes
on distinguished analytic stable triangles.  The raw stable category is
triangulated, not abelian; the canonical exactness statement is therefore the
exactness of the short complex after applying preadditive covariant or
contravariant Yoneda functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Covariant preadditive Yoneda sends the short complex of a distinguished
analytic stable triangle to an exact short complex of abelian groups. -/
theorem TraceAnalyticStableMotiveQuasicategory.coyonedaShortComplex_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle triangle distinguished).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  (preadditiveCoyoneda.obj probe).map_distinguished_exact
    triangle
    distinguished

/-- Contravariant preadditive Yoneda sends the opposite short complex of a
distinguished analytic stable triangle to an exact short complex of abelian
groups. -/
theorem TraceAnalyticStableMotiveQuasicategory.yonedaShortComplex_exact
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .shortComplexOfDistinguishedTriangle triangle distinguished).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  Pretriangulated.preadditiveYoneda_map_distinguished
    triangle
    distinguished
    probe

/-- Covariant preadditive Yoneda exactness for the chosen cofiber triangle of
a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberCoyonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ) :
    ((TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .coyonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle_distinguished morphism)
      probe

/-- Contravariant preadditive Yoneda exactness for the chosen cofiber
triangle of a morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.cofiberYonedaShortComplex_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticStableMotiveQuasicategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  TraceAnalyticStableMotiveQuasicategory
    .yonedaShortComplex_exact
      (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle morphism)
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle_distinguished morphism)
      probe

end AnalyticMotives
end LFunctions
end Boundary
