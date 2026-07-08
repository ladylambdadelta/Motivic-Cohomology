import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level rotated cofiber triangle projections

This owner file exposes the displayed maps of the package-level rotated and
inverse-rotated chosen cofiber triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The first map of the package-level rotated cofiber triangle is the chosen
cofiber cocone map. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
      morphism).mor₁ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism :=
  rfl

/-- The second map of the package-level rotated cofiber triangle is the
chosen cofiber boundary map. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
      morphism).mor₂ =
      traceAnalyticStableInfinityCategory.cofiberBoundary morphism :=
  rfl

/-- The third map of the package-level rotated cofiber triangle is the
shifted negative original morphism. -/
theorem traceAnalyticStableInfinityCategory_rotatedCofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.rotatedCofiberTriangle
      morphism).mor₃ =
      -morphism⟦(1 : ℤ)⟧' :=
  rfl

/-- The first map of the package-level inverse-rotated cofiber triangle is
the shifted negative boundary followed by the unit comparison. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
      morphism).mor₁ =
      -((traceAnalyticStableInfinityCategory.cofiberBoundary
        morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the package-level inverse-rotated cofiber triangle is
the original morphism. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
      morphism).mor₂ =
      morphism :=
  rfl

/-- The third map of the package-level inverse-rotated cofiber triangle is
the chosen cocone map followed by the counit comparison. -/
theorem traceAnalyticStableInfinityCategory_invRotatedCofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory.invRotatedCofiberTriangle
      morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
