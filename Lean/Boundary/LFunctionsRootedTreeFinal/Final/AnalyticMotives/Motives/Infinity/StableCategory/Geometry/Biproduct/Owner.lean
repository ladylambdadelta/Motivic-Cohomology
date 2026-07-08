import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner

/-!
# Binary biproduct triangles in the analytic stable motive category

This owner file exposes the distinguished binary biproduct and binary product
triangles supplied by the triangulated structure on analytic stable motives.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The binary biproduct triangle of two analytic stable motives. -/
def TraceAnalyticStableMotiveQuasicategory.binaryBiproductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    StableInfinityOwner.PresentedTriangle :=
  Pretriangulated.binaryBiproductTriangle left right

/-- The binary product triangle of two analytic stable motives. -/
def TraceAnalyticStableMotiveQuasicategory.binaryProductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    StableInfinityOwner.PresentedTriangle :=
  Pretriangulated.binaryProductTriangle left right

/-- Binary biproduct triangles are distinguished in the analytic stable
motive category. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryBiproductTriangle_distinguished
    (left right : StableInfinityOwner.PresentedCategory) :
    TraceAnalyticStableMotiveQuasicategory
        .binaryBiproductTriangle left right ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.binaryBiproductTriangle_distinguished left right

/-- Binary product triangles are distinguished in the analytic stable motive
category. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.binaryProductTriangle_distinguished
    (left right : StableInfinityOwner.PresentedCategory) :
    TraceAnalyticStableMotiveQuasicategory
        .binaryProductTriangle left right ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.binaryProductTriangle_distinguished left right

/-- The binary product triangle is canonically isomorphic to the binary
biproduct triangle. -/
def TraceAnalyticStableMotiveQuasicategory.binaryProductTriangleIsoBinaryBiproductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    TraceAnalyticStableMotiveQuasicategory.binaryProductTriangle left right ≅
      TraceAnalyticStableMotiveQuasicategory.binaryBiproductTriangle
        left right :=
  Pretriangulated.binaryProductTriangleIsoBinaryBiproductTriangle left right

end AnalyticMotives
end LFunctions
end Boundary
