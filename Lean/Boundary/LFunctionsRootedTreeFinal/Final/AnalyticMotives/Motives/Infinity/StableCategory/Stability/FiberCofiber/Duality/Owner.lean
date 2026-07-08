import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Fiber.Comparison.Owner

/-!
# Fiber-cofiber duality in analytic stable motives

This owner file exposes the stable-category identity behind the fiber
construction: the chosen fiber of a morphism is the desuspended chosen cofiber,
and the two nontrivial fiber boundary maps are the desuspended cofiber boundary
and the shifted cofiber cocone map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen fiber object is the negative unit shift of the chosen cofiber
object. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberObject_eq_cofiber_shift_neg
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberObject morphism =
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberObject morphism)⟦(-1 : ℤ)⟧ :=
  rfl

/-- The chosen fiber map is the desuspended negative cofiber boundary,
transported through the unit comparison of the shift equivalence. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberMap_eq_cofiberBoundary_shift
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberMap morphism =
      -((TraceAnalyticStableMotiveQuasicategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The third map of the chosen fiber triangle is the cofiber cocone map,
transported through the counit comparison of the shift equivalence. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberConnectingMap_eq_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).mor₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

/-- The chosen fiber triangle is the inverse rotation of the chosen cofiber
triangle, written as the stable fiber/cofiber duality statement. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_eq_invRotate_cofiber
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism =
      (TraceAnalyticStableMotiveQuasicategory
        .cofiberTriangle morphism).invRotate :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
