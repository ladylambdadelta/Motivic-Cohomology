import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Full.Projections.Owner

/-!
# Triangle projections from the full current stable fragment

This file peels the exact-triangle component of the full current stable
package into individual triangle distinguishedness and inverse-rotation
fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The full current package gives distinguishedness of the chosen cofiber
triangle. -/
theorem traceAnalyticStableInfinityCategory_current_full_cofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).left.left

/-- The full current package gives distinguishedness of the chosen fiber
triangle. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).left.right.left

/-- The full current package identifies the chosen fiber triangle with the
inverse rotation of the chosen cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberTriangle_eq_invRotate
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberTriangle morphism).invRotate :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).left.right.right

end AnalyticMotives
end LFunctions
end Boundary
