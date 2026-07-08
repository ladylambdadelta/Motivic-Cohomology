import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level binary biproduct triangles

This owner file exposes binary biproduct and binary product triangles through
the assembled `traceAnalyticStableInfinityCategory` package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level binary biproduct triangle of two analytic stable
motives. -/
def traceAnalyticStableInfinityCategory_binaryBiproductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    StableInfinityOwner.PresentedTriangle :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductTriangle left right

/-- The package-level binary product triangle of two analytic stable
motives. -/
def traceAnalyticStableInfinityCategory_binaryProductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    StableInfinityOwner.PresentedTriangle :=
  traceAnalyticStableInfinityCategory
    .binaryProductTriangle left right

/-- Package-level binary biproduct triangles are distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductTriangle_distinguished
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_binaryBiproductTriangle
        left right ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductTriangle_distinguished left right

/-- Package-level binary product triangles are distinguished. -/
theorem
    traceAnalyticStableInfinityCategory_binaryProductTriangle_distinguished
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_binaryProductTriangle
        left right ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .binaryProductTriangle_distinguished left right

/-- The package-level binary product triangle is canonically isomorphic to
the package-level binary biproduct triangle. -/
def
    traceAnalyticStableInfinityCategory_binaryProductTriangleIsoBinaryBiproductTriangle
    (left right : StableInfinityOwner.PresentedCategory) :
    traceAnalyticStableInfinityCategory_binaryProductTriangle left right ≅
      traceAnalyticStableInfinityCategory_binaryBiproductTriangle
        left right :=
  traceAnalyticStableInfinityCategory
    .binaryProductTriangleIsoBinaryBiproductTriangle left right

end AnalyticMotives
end LFunctions
end Boundary
