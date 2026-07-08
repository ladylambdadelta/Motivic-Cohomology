import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.YonedaExact.Rotations.Owner

/-!
# Projections from global rotated cofiber Yoneda exactness

This file exposes the four exactness projections for rotated and
inverse-rotated cofiber short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Rotated cofiber short complexes are exact after covariant preadditive
Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_rotatedCofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate
    morphism
    probe
    rightProbe).left

/-- Rotated cofiber short complexes are exact after contravariant
preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate
    morphism
    leftProbe
    probe).right.left

/-- Inverse-rotated cofiber short complexes are exact after covariant
preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_invRotatedCofiber_coyoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (probe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).map
        (preadditiveCoyoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate
    morphism
    probe
    rightProbe).right.right.left

/-- Inverse-rotated cofiber short complexes are exact after contravariant
preadditive Yoneda evaluation. -/
theorem
    traceAnalyticStableInfinityCategory_global_invRotatedCofiber_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (probe : StableInfinityOwner.PresentedCategory) :
    ((traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).op.map
        (preadditiveYoneda.obj probe)).Exact :=
  (traceAnalyticStableInfinityCategory_global_rotatedCofiber_yoneda_exact_certificate
    morphism
    leftProbe
    probe).right.right.right

end AnalyticMotives
end LFunctions
end Boundary
