import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Full.Projections.Owner

/-!
# Individual field projections from the full current stable fragment

This file peels the exact-triangle component of the full current stable
package into individual zero-composition and Yoneda-exactness fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The full current package gives the first cofiber zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_full_morphism_comp_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    morphism ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.left.left

/-- The full current package gives the second cofiber zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_full_cofiberCocone_comp_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.left.right.left

/-- The full current package gives the shifted cofiber-boundary
zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_full_cofiberBoundary_comp_shift
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.left.right.right.left

/-- The full current package gives the fiber-map zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberMap_comp_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberMap morphism ≫ morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.left.right.right.right

/-- The full current package gives covariant preadditive Yoneda exactness for
the cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_full_cofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.left.left

/-- The full current package gives covariant preadditive Yoneda exactness for
the fiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.left.right

/-- The full current package gives contravariant preadditive Yoneda exactness
for the cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_full_cofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.right.left

/-- The full current package gives contravariant preadditive Yoneda exactness
for the fiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_full_exactTriangle_fragment
    morphism
    leftProbe
    rightProbe).right.right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
