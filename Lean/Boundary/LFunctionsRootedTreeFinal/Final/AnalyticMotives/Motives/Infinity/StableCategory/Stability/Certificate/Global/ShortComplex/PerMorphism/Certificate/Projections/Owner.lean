import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ShortComplex.PerMorphism.Certificate.Owner

/-!
# Projections from the global per-morphism short-complex certificate

This file exposes the map-shape, zero-composition, and Yoneda-exactness
components of the full per-morphism certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Projection to the map-shape component of the full short-complex
certificate. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate_shape
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
      morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).left

/-- Projection to the zero-composition component of the full short-complex
certificate. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate_zeroComposition
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
      morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).right.left

/-- Projection to the Yoneda-exactness component of the full short-complex
certificate. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate_yoneda_exact
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_global_perMorphism_yoneda_exact
      morphism
      leftProbe
      rightProbe :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_certificate
    morphism
    leftProbe
    rightProbe).right.right

end AnalyticMotives
end LFunctions
end Boundary
