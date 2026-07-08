import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level projections for rotated cofiber short complexes

This owner file exposes the two maps of the package-level rotated and
inverse-rotated chosen cofiber short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first map of the package-level rotated cofiber short complex is the
chosen cofiber cocone map. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).f =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The second map of the package-level rotated cofiber short complex is the
chosen cofiber boundary map. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberShortComplex
      morphism).g =
      traceAnalyticStableInfinityCategory.cofiberBoundary morphism :=
  rfl

/-- The first map of the package-level inverse-rotated cofiber short complex
is the shifted negative boundary followed by the unit comparison. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_f
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.invRotatedCofiberShortComplex
      morphism).f =
      -((traceAnalyticStableInfinityCategory.cofiberBoundary
        morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the package-level inverse-rotated cofiber short complex
is the original morphism. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberShortComplex_g
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.invRotatedCofiberShortComplex
      morphism).g =
      morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
