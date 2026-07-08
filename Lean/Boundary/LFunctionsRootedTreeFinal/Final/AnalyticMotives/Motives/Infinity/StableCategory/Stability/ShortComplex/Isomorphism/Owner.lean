import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.ShortComplex.Owner

/-!
# Isomorphisms of short complexes attached to isomorphic triangles

This owner file exposes the short-complex isomorphism induced by an
isomorphism of distinguished analytic stable triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The isomorphism between short complexes attached to isomorphic
distinguished analytic stable triangles. -/
def
    TraceAnalyticStableMotiveQuasicategory.shortComplexIsoOfTriangleIso
    {first second : StableInfinityOwner.PresentedTriangle}
    (triangleIso : first ≅ second)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    TraceAnalyticStableMotiveQuasicategory
        .shortComplexOfDistinguishedTriangle
        first
        first_distinguished ≅
      TraceAnalyticStableMotiveQuasicategory
        .shortComplexOfDistinguishedTriangle
        second
        (TraceAnalyticStableMotiveQuasicategory
          .distinguished_of_triangleIso
          triangleIso
          first_distinguished) :=
  Pretriangulated.shortComplexOfDistTriangleIsoOfIso
    triangleIso
    first_distinguished

/-- The short-complex isomorphism induced by a triangle isomorphism is
Mathlib's short-complex isomorphism for distinguished triangles. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.shortComplexIsoOfTriangleIso_eq
    {first second : StableInfinityOwner.PresentedTriangle}
    (triangleIso : first ≅ second)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles) :
    TraceAnalyticStableMotiveQuasicategory.shortComplexIsoOfTriangleIso
        triangleIso
        first_distinguished =
      Pretriangulated.shortComplexOfDistTriangleIsoOfIso
        triangleIso
        first_distinguished :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
