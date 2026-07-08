import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Projections.Owner

/-!
# Triangle projections from current stable fragments

This file peels the grouped current triangle-stability projection into the
individual cofiber distinguishedness, fiber distinguishedness, and inverse
rotation fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The current fragment gives distinguishedness of the chosen cofiber
triangle. -/
theorem traceAnalyticStableInfinityCategory_current_cofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_current_triangle_stability
    morphism
    leftProbe
    rightProbe).left

/-- The current fragment gives distinguishedness of the chosen fiber
triangle. -/
theorem traceAnalyticStableInfinityCategory_current_fiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_current_triangle_stability
    morphism
    leftProbe
    rightProbe).right.left

/-- The current fragment identifies the chosen fiber triangle with the
inverse rotation of the chosen cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_current_fiberTriangle_eq_invRotate
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberTriangle morphism).invRotate :=
  (traceAnalyticStableInfinityCategory_current_triangle_stability
    morphism
    leftProbe
    rightProbe).right.right

end AnalyticMotives
end LFunctions
end Boundary
