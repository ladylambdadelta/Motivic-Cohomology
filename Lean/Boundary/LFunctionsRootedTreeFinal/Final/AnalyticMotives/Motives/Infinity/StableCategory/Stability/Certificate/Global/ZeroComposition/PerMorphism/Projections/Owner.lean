import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Certificate.Global.ZeroComposition.PerMorphism.Owner

/-!
# Projections from global per-morphism zero-composition fields

This file exposes the four zero-field projections for the canonical short
complexes attached to one morphism in the analytic stable category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen cofiber short complex carries its canonical zero field. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_cofiber_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .cofiber_morphism_comp_cocone morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
    morphism).left

/-- The chosen fiber short complex carries its canonical zero field. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_fiber_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).zero =
        traceAnalyticStableInfinityCategory
          .fiberMap_comp_morphism morphism :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
    morphism).right.left

/-- The rotated cofiber short complex carries its canonical zero field. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_rotatedCofiber_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₁_comp_mor₂
          (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
            morphism)
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle_distinguished morphism) :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
    morphism).right.right.left

/-- The inverse-rotated cofiber short complex carries its canonical zero
field. -/
theorem
    traceAnalyticStableInfinityCategory_global_perMorphism_invRotatedCofiber_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₁_comp_mor₂
          (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
            morphism)
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle_distinguished morphism) :=
  (traceAnalyticStableInfinityCategory_global_perMorphism_zeroComposition
    morphism).right.right.right

end AnalyticMotives
end LFunctions
end Boundary
