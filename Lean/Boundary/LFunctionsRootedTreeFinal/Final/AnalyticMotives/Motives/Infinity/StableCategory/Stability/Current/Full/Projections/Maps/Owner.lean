import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Current.Full.Projections.Owner

/-!
# Map projections from the full current stable fragment

This file exposes the map-level fiber/cofiber identities from the full
current stable package under a dedicated map-projection import path.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The full current package identifies the chosen fiber map with the
desuspended negative cofiber boundary map. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberMap_desuspended_boundary
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory.fiberMap morphism =
      -((traceAnalyticStableInfinityCategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory_current_full_fiberMap_identity
    morphism
    leftProbe
    rightProbe

/-- The full current package identifies the chosen fiber connecting map with
the cofiber cocone map followed by the unit-shift counit inverse. -/
theorem traceAnalyticStableInfinityCategory_current_full_fiberConnectingMap_cofiberCocone
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target)
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory
      .fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  traceAnalyticStableInfinityCategory_current_full_connecting_identity
    morphism
    leftProbe
    rightProbe

end AnalyticMotives
end LFunctions
end Boundary
