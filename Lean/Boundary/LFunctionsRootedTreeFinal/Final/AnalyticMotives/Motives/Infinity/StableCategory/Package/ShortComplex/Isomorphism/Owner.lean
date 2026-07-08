import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level short-complex isomorphism identification

This owner file identifies the package-level short-complex isomorphism
attached to a triangle isomorphism with Mathlib's pretriangulated
short-complex isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level short-complex isomorphism attached to a triangle
isomorphism is Mathlib's pretriangulated short-complex isomorphism. -/
theorem traceAnalyticStableInfinityCategory_shortComplexIsoOfTriangleIso_eq
    {first second : StableInfinityOwner.PresentedTriangle}
    (triangleIso : first ≅ second)
    (first_distinguished :
      first ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    traceAnalyticStableInfinityCategory.shortComplexIsoOfTriangleIso
        triangleIso
        first_distinguished =
      Pretriangulated.shortComplexOfDistTriangleIsoOfIso
        triangleIso
        first_distinguished :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
