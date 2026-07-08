import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level zero fields for rotated cofiber short complexes

This owner file exposes the zero fields of the package-level rotated and
inverse-rotated chosen cofiber short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The zero field of the package-level rotated cofiber short complex is the
first zero-composition law for the package-level rotated cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .rotatedCofiberShortComplex morphism).zero =
      traceAnalyticStableInfinityCategory
        .distinguishedTriangle_mor₁_comp_mor₂
        (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
          morphism)
        (traceAnalyticStableInfinityCategory
          .rotatedCofiberTriangle_distinguished morphism) :=
  rfl

/-- The zero field of the package-level inverse-rotated cofiber short complex
is the first zero-composition law for the package-level inverse-rotated
cofiber triangle. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_zero
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory
      .invRotatedCofiberShortComplex morphism).zero =
      traceAnalyticStableInfinityCategory
        .distinguishedTriangle_mor₁_comp_mor₂
        (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
          morphism)
        (traceAnalyticStableInfinityCategory
          .invRotatedCofiberTriangle_distinguished morphism) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
