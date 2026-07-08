import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level projections for distinguished-triangle short complexes

This owner file exposes the two maps of the package-level short complex
attached to a distinguished analytic stable triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first map of the package-level short complex attached to a
distinguished triangle is the first map of that triangle. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexOfDistinguishedTriangle_f
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    (traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).f =
      triangle.mor₁ :=
  rfl

/-- The second map of the package-level short complex attached to a
distinguished triangle is the second map of that triangle. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexOfDistinguishedTriangle_g
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    (traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).g =
      triangle.mor₂ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
