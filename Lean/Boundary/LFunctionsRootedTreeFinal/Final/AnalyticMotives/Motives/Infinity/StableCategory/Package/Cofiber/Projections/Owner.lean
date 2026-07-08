import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level cofiber triangle projections

This owner file exposes the three displayed maps of the package-level chosen
cofiber triangle through the assembled `traceAnalyticStableInfinityCategory`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level chosen cofiber triangle has the original morphism as
its first map. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberTriangle morphism).mor₁ =
      morphism :=
  rfl

/-- The package-level chosen cofiber triangle has the chosen cocone map as
its second map. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberTriangle morphism).mor₂ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The package-level chosen cofiber triangle has the chosen boundary map as
its third map. -/
theorem traceAnalyticStableInfinityCategory_cofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.cofiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberBoundary morphism :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
