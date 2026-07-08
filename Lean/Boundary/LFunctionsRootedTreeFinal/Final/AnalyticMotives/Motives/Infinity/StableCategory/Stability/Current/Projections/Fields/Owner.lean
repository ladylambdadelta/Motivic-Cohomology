import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Projections.Owner

/-!
# Individual projections from current stable fragments

This file peels the grouped current stable-fragment projections into the
single cofiber/fiber zero-composition and Yoneda-exactness fields used by
downstream exact-triangle arguments.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The current fragment gives the first cofiber zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_morphism_comp_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    morphism ≫
        traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_zero_compositions
    morphism
    leftProbe
    rightProbe).left

/-- The current fragment gives the second cofiber zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_cofiberCocone_comp_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        traceAnalyticStableInfinityCategory.cofiberBoundary morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_zero_compositions
    morphism
    leftProbe
    rightProbe).right.left

/-- The current fragment gives the shifted cofiber-boundary
zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_cofiberBoundary_comp_shift
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.cofiberBoundary morphism ≫
        morphism⟦(1 : ℤ)⟧' =
      0 :=
  (traceAnalyticStableInfinityCategory_current_zero_compositions
    morphism
    leftProbe
    rightProbe).right.right.left

/-- The current fragment gives the fiber-map zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_current_fiberMap_comp_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberMap morphism ≫ morphism =
      0 :=
  (traceAnalyticStableInfinityCategory_current_zero_compositions
    morphism
    leftProbe
    rightProbe).right.right.right

/-- The current fragment gives covariant preadditive Yoneda exactness for the
cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_cofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_coyoneda_exact
    morphism
    leftProbe
    rightProbe).left

/-- The current fragment gives covariant preadditive Yoneda exactness for the
fiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_fiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_coyoneda_exact
    morphism
    leftProbe
    rightProbe).right

/-- The current fragment gives contravariant preadditive Yoneda exactness for
the cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_cofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_yoneda_exact
    morphism
    leftProbe
    rightProbe).left

/-- The current fragment gives contravariant preadditive Yoneda exactness for
the fiber short complex. -/
theorem traceAnalyticStableInfinityCategory_current_fiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_current_yoneda_exact
    morphism
    leftProbe
    rightProbe).right

end AnalyticMotives
end LFunctions
end Boundary
