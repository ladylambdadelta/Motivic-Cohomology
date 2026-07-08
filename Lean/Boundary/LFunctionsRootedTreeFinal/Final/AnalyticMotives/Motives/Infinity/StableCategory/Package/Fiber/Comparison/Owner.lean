import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.ShortComplex.Fiber.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Owner

/-!
# Package-level comparison of fiber and inverse-rotated cofiber data

This owner file exposes through `traceAnalyticStableInfinityCategory` that the
semantic fiber data are the inverse-rotated chosen cofiber data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level chosen fiber object is the first vertex of the
inverse-rotated chosen cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_fiberObject_eq_invRotated_obj₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberObject morphism =
      (traceAnalyticStableInfinityCategory
        .invRotatedCofiberTriangle morphism).obj₁ :=
  rfl

/-- The package-level chosen fiber map is the first edge of the
inverse-rotated chosen cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_fiberMap_eq_invRotated_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberMap morphism =
      (traceAnalyticStableInfinityCategory
        .invRotatedCofiberTriangle morphism).mor₁ :=
  rfl

/-- The package-level chosen fiber triangle is the inverse-rotated chosen
cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangle morphism =
      traceAnalyticStableInfinityCategory
        .invRotatedCofiberTriangle morphism :=
  rfl

/-- The package-level chosen fiber short complex is the inverse-rotated
chosen cofiber short complex. -/
theorem traceAnalyticStableInfinityCategory_fiberShortComplex_eq_invRotated
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberShortComplex morphism =
      traceAnalyticStableInfinityCategory
        .invRotatedCofiberShortComplex morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
