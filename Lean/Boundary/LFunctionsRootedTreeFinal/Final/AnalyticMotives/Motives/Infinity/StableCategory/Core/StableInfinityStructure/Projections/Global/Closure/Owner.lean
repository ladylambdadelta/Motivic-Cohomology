import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.StableInfinityStructure.Projections.Global.Owner

/-!
# Closure projections from the actual global stability certificate

This file exposes one-direction closure consequences of the actual
stable-infinity global stability certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The actual stable-infinity certificate makes contractible triangles
distinguished. -/
theorem traceAnalyticStableInfinityCategory_actual_global_contractibleTriangle_mem
    (object : StableInfinityOwner.PresentedCategory) :
    Pretriangulated.contractibleTriangle object ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory_actual_global_contractible_distinguished
    object

/-- The actual stable-infinity certificate sends distinguished triangles to
distinguished rotated triangles. -/
theorem traceAnalyticStableInfinityCategory_actual_global_rotate_mem
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle.rotate ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_actual_global_rotate_distinguished
    triangle).mp
    distinguished

/-- The actual stable-infinity certificate reflects distinguishedness along
triangle rotation. -/
theorem traceAnalyticStableInfinityCategory_actual_global_of_rotate_mem
    (triangle : StableInfinityOwner.PresentedTriangle)
    (rotated :
      triangle.rotate ∈
        traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  (traceAnalyticStableInfinityCategory_actual_global_rotate_distinguished
    triangle).mpr
    rotated

end AnalyticMotives
end LFunctions
end Boundary
