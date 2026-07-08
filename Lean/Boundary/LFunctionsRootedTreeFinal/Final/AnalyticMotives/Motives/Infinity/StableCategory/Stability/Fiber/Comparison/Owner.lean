import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Fiber.Owner

/-!
# Comparison of fiber data with inverse-rotated cofiber data

This owner file records that the semantic fiber data are definitionally the
corresponding data read from the inverse-rotated chosen cofiber triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen fiber object is the first vertex of the inverse-rotated chosen
cofiber triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberObject_eq_invRotated_obj₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberObject morphism =
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle morphism).obj₁ :=
  rfl

/-- The chosen fiber map is the first edge of the inverse-rotated chosen
cofiber triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberMap_eq_invRotated_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberMap morphism =
      (TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle morphism).mor₁ :=
  rfl

/-- The chosen fiber triangle is the inverse-rotated chosen cofiber
triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberTriangle morphism :=
  rfl

/-- The chosen fiber short complex is the inverse-rotated chosen cofiber
short complex. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.fiberShortComplex_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberShortComplex morphism =
      TraceAnalyticStableMotiveQuasicategory
        .invRotatedCofiberShortComplex morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
