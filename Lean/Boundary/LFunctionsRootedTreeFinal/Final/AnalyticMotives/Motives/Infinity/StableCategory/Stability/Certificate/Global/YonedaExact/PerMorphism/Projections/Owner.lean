import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.YonedaExact.PerMorphism.Owner

/-!
# Projections from global per-morphism Yoneda exactness

This file exposes the eight exactness projections for the canonical short
complexes attached to one morphism in the analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Cofiber short complexes are exact after covariant Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_cofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).left

/-- Cofiber short complexes are exact after contravariant Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_cofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.left

/-- Fiber short complexes are exact after covariant Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_fiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.left

/-- Fiber short complexes are exact after contravariant Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_fiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .fiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.left

/-- Rotated cofiber short complexes are exact after covariant Yoneda
evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_rotatedCofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.left

/-- Rotated cofiber short complexes are exact after contravariant Yoneda
evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_rotatedCofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.left

/-- Inverse-rotated cofiber short complexes are exact after covariant Yoneda
evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_invRotatedCofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj leftProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.left

/-- Inverse-rotated cofiber short complexes are exact after contravariant
Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_invRotatedCofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj rightProbe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
