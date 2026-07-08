import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Biproduct.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.TriangleGeometry.Biproduct.Owner

/-!
# Package-level short complexes for binary biproduct triangles

This owner file exposes short complexes attached to package-level binary
biproduct and binary product triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level short complex attached to the binary biproduct
triangle. -/
def traceAnalyticStableInfinityCategory_binaryBiproductShortComplex
    (left right : StableInfinityOwner.PresentedCategory) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory
    .binaryBiproductShortComplex left right

/-- The first map of the package-level binary biproduct short complex. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductShortComplex_f
    (left right : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory_binaryBiproductShortComplex
      left right).f =
      (traceAnalyticStableInfinityCategory_binaryBiproductTriangle
        left right).mor₁ :=
  rfl

/-- The second map of the package-level binary biproduct short complex. -/
theorem
    traceAnalyticStableInfinityCategory_binaryBiproductShortComplex_g
    (left right : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory_binaryBiproductShortComplex
      left right).g =
      (traceAnalyticStableInfinityCategory_binaryBiproductTriangle
        left right).mor₂ :=
  rfl

/-- The package-level short complex attached to the binary product
triangle. -/
def traceAnalyticStableInfinityCategory_binaryProductShortComplex
    (left right : StableInfinityOwner.PresentedCategory) :
    ShortComplex StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory
    .binaryProductShortComplex left right

/-- The first map of the package-level binary product short complex. -/
theorem traceAnalyticStableInfinityCategory_binaryProductShortComplex_f
    (left right : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory_binaryProductShortComplex
      left right).f =
      (traceAnalyticStableInfinityCategory_binaryProductTriangle
        left right).mor₁ :=
  rfl

/-- The second map of the package-level binary product short complex. -/
theorem traceAnalyticStableInfinityCategory_binaryProductShortComplex_g
    (left right : StableInfinityOwner.PresentedCategory) :
    (traceAnalyticStableInfinityCategory_binaryProductShortComplex
      left right).g =
      (traceAnalyticStableInfinityCategory_binaryProductTriangle
        left right).mor₂ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
