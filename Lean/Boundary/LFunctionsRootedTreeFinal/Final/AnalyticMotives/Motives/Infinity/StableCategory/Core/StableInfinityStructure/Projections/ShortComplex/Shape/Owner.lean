import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.ShortComplex.Owner

/-!
# Per-morphism short-complex shape projections from the actual stable-infinity certificate

This file peels the eight map-identification fields for the canonical
per-morphism short complexes out of the actual stable-infinity structure
certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The cofiber short complex has the original morphism as its first map. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_cofiber_f
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).f =
      morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).left

/-- The cofiber short complex has the chosen cocone map as its second map. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_cofiber_g
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory.cofiberShortComplex morphism).g =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.left

/-- The fiber short complex has the chosen fiber map as its first map. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_fiber_f
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex morphism).f =
      traceAnalyticStableInfinityCategory.fiberMap morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.left

/-- The fiber short complex has the original morphism as its second map. -/
theorem traceAnalyticStableInfinityCategory_actual_shortComplex_fiber_g
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory_fiberShortComplex morphism).g =
      morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.right.left

/-- The rotated cofiber short complex has the chosen cocone map as its first
map. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_rotatedCofiber_f
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).f =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.right.right.left

/-- The rotated cofiber short complex has the chosen boundary map as its
second map. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_rotatedCofiber_g
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).g =
      traceAnalyticStableInfinityCategory.cofiberBoundary morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.left

/-- The inverse-rotated cofiber short complex has the desuspended negative
boundary map as its first map. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_invRotatedCofiber_f
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).f =
      -((traceAnalyticStableInfinityCategory.cofiberBoundary
        morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.left

/-- The inverse-rotated cofiber short complex has the original morphism as its
second map. -/
theorem
    traceAnalyticStableInfinityCategory_actual_shortComplex_invRotatedCofiber_g
    {source target : TraceAnalyticStableInfinityCategory.HomotopyCategory}
    (morphism : source ⟶ target)
    (leftProbe : TraceAnalyticStableInfinityCategory.HomotopyCategoryᵒᵖ)
    (rightProbe : TraceAnalyticStableInfinityCategory.HomotopyCategory) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).g =
      morphism :=
  (traceAnalyticStableInfinityCategory_actual_shortComplex_shape
    morphism
    leftProbe
    rightProbe).right.right.right.right.right.right.right

end AnalyticMotives
end LFunctions
end Boundary
