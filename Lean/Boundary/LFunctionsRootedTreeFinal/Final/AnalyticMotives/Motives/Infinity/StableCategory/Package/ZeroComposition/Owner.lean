import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level zero fields for analytic stable motive short complexes

This owner file exposes the zero fields of short complexes through the
assembled `traceAnalyticStableInfinityCategory` package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zero field of the package-level short complex attached to a
distinguished triangle is the package-level first zero-composition law. -/
theorem
    traceAnalyticStableInfinityCategory_shortComplexOfDistinguishedTriangle_zero
    (triangle : StableInfinityOwner.PresentedTriangle)
    (distinguished :
      triangle ∈ traceAnalyticStableInfinityCategory.distinguishedTriangles) :
    (traceAnalyticStableInfinityCategory
      .shortComplexOfDistinguishedTriangle
        triangle
        distinguished).zero =
      traceAnalyticStableInfinityCategory
        .distinguishedTriangle_mor₁_comp_mor₂
        triangle
        distinguished :=
  rfl

/-- The zero field of the package-level chosen cofiber short complex is the
package-level chosen cofiber zero-composition law. -/
theorem traceAnalyticStableInfinityCategory_cofiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .cofiberShortComplex morphism).zero =
      traceAnalyticStableInfinityCategory
        .cofiber_morphism_comp_cocone morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
