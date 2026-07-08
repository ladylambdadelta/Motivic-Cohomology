import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ShortComplex.PerMorphism.Owner

/-!
# Projections from global per-morphism short-complex shape

This file exposes the eight map-identification projections for the canonical
short complexes attached to one morphism in the analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first cofiber short-complex map is the original morphism. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_cofiber_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).f =
      morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).left

/-- The second cofiber short-complex map is the chosen cocone map. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_cofiber_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).g =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.left

/-- The first fiber short-complex map is the chosen fiber map. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_fiber_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex morphism).f =
      traceAnalyticStableInfinityCategory.fiberMap morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.left

/-- The second fiber short-complex map is the original morphism. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_fiber_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex morphism).g =
      morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.right.left

/-- The first rotated cofiber short-complex map is the chosen cocone map. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_rotatedCofiber_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).f =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.right.right.left

/-- The second rotated cofiber short-complex map is the chosen boundary map. -/
theorem traceAnalyticStableInfinityCategory_global_perMorphism_rotatedCofiber_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).g =
      traceAnalyticStableInfinityCategory.cofiberBoundary morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.right.right.right.left

/-- The first inverse-rotated cofiber short-complex map is the desuspended
negative boundary map. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_invRotatedCofiber_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).f =
      -((traceAnalyticStableInfinityCategory.cofiberBoundary
        morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.right.right.right.right.left

/-- The second inverse-rotated cofiber short-complex map is the original
morphism. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_invRotatedCofiber_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).g =
      morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_shortComplex_shape
    morphism).right.right.right.right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
