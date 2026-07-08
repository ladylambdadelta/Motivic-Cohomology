import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.ShortComplex.Owner

/-!
# Per-morphism zero-composition projections from the actual stable-infinity certificate

This file peels the four zero-composition fields for the canonical
per-morphism short complexes out of the actual stable-infinity structure
certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate supplies the canonical zero field
for the cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_cofiber_zero
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .cofiber_morphism_comp_cocone morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_zeroComposition
    morphism
    leftProbe
    rightProbe).left

/-- The actual stable-infinity certificate supplies the canonical zero field
for the fiber short complex. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_fiber_zero
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex
      morphism).zero =
        traceAnalyticStableInfinityCategory
          .fiberMap_comp_morphism morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_zeroComposition
    morphism
    leftProbe
    rightProbe).right.left

/-- The actual stable-infinity certificate supplies the canonical zero field
for the rotated cofiber short complex. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_rotatedCofiber_zero
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₁_comp_mor₂
          (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
            morphism)
          (traceAnalyticStableInfinityCategory
            .rotatedCofiberTriangle_distinguished morphism) :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_zeroComposition
    morphism
    leftProbe
    rightProbe).right.right.left

/-- The actual stable-infinity certificate supplies the canonical zero field
for the inverse-rotated cofiber short complex. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_invRotatedCofiber_zero
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).zero =
        traceAnalyticStableInfinityCategory
          .distinguishedTriangle_mor₁_comp_mor₂
          (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
            morphism)
          (traceAnalyticStableInfinityCategory
            .invRotatedCofiberTriangle_distinguished morphism) :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_zeroComposition
    morphism
    leftProbe
    rightProbe).right.right.right

end AnalyticMotives
end LFunctions
end Boundary
