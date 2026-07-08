import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Owner

/-!
# Map projections from current stable fragments

This file exposes the map-level fiber/cofiber duality already proved in the
bicartesian stability surface, under the current stable-fragment hierarchy.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The current stability surface identifies the chosen fiber map with the
desuspended negative cofiber boundary map. -/
theorem traceAnalyticStableInfinityCategory_current_fiberMap_desuspended_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory_fiberMap_is_desuspended_boundary
    morphism

/-- The current stability surface identifies the chosen fiber connecting map
with the cofiber cocone map followed by the unit-shift counit inverse. -/
theorem traceAnalyticStableInfinityCategory_current_fiberConnectingMap_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory_fiberConnectingMap_is_cofiberCocone
    morphism

end AnalyticMotives
end LFunctions
end Boundary
