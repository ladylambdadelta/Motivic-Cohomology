import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.Fiber.Comparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.FiberCofiber.Duality.Owner

/-!
# Package-level fiber-cofiber duality

This owner file exposes through `traceAnalyticStableInfinityCategory` the
stable-category identity that fibers are desuspended cofibers.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Package-level chosen fibers are negative unit shifts of package-level
chosen cofibers. -/
theorem traceAnalyticStableInfinityCategory_fiberObject_eq_cofiber_shift_neg
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberObject morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberObject morphism)⟦(-1 : ℤ)⟧ :=
  traceAnalyticStableInfinityCategory
    .fiberObject_eq_cofiber_shift_neg morphism

/-- Package-level chosen fiber maps are desuspended negative cofiber
boundaries, transported through the unit comparison of the shift equivalence. -/
theorem traceAnalyticStableInfinityCategory_fiberMap_eq_cofiberBoundary_shift
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory
    .fiberMap_eq_cofiberBoundary_shift morphism

/-- The third map of the package-level chosen fiber triangle is the cofiber
cocone map transported through the counit comparison. -/
theorem traceAnalyticStableInfinityCategory_fiberConnectingMap_eq_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory
    .fiberConnectingMap_eq_cofiberCocone morphism

/-- Package-level chosen fiber triangles are inverse rotations of chosen
cofiber triangles. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_eq_invRotate_cofiber
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberTriangle morphism =
      (traceAnalyticStableInfinityCategory
        .cofiberTriangle morphism).invRotate :=
  traceAnalyticStableInfinityCategory
    .fiberTriangle_eq_invRotate_cofiber morphism

end AnalyticMotives
end LFunctions
end Boundary
