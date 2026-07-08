import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level fiber triangle projections

This owner file exposes the chosen fiber object, fiber map, and fiber triangle
through the assembled `traceAnalyticStableInfinityCategory` package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level chosen fiber object is the first object of the
inverse-rotated chosen cofiber triangle. -/
def traceAnalyticStableInfinityCategory_fiberObject
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedCategory :=
  traceAnalyticStableInfinityCategory.fiberObject morphism

/-- The package-level chosen fiber map is the first map of the
inverse-rotated chosen cofiber triangle. -/
def traceAnalyticStableInfinityCategory_fiberMap
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberObject morphism ⟶ source :=
  traceAnalyticStableInfinityCategory.fiberMap morphism

/-- The package-level chosen fiber triangle is the inverse-rotated chosen
cofiber triangle. -/
def traceAnalyticStableInfinityCategory_fiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  traceAnalyticStableInfinityCategory.fiberTriangle morphism

/-- The package-level chosen fiber triangle is distinguished. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberTriangle morphism ∈
      traceAnalyticStableInfinityCategory.distinguishedTriangles :=
  traceAnalyticStableInfinityCategory
    .fiberTriangle_distinguished morphism

/-- The first object of the package-level chosen fiber triangle is the
chosen fiber object. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_obj₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).obj₁ =
      traceAnalyticStableInfinityCategory_fiberObject morphism :=
  rfl

/-- The second object of the package-level chosen fiber triangle is the
source of the original morphism. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_obj₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).obj₂ =
      source :=
  rfl

/-- The third object of the package-level chosen fiber triangle is the target
of the original morphism. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_obj₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).obj₃ =
      target :=
  rfl

/-- The first map of the package-level chosen fiber triangle is the chosen
fiber map. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).mor₁ =
      traceAnalyticStableInfinityCategory_fiberMap morphism :=
  rfl

/-- The second map of the package-level chosen fiber triangle is the original
morphism. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).mor₂ =
      morphism :=
  rfl

/-- The third map of the package-level chosen fiber triangle is the
inverse-rotated connecting map. -/
theorem traceAnalyticStableInfinityCategory_fiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (traceAnalyticStableInfinityCategory_fiberTriangle morphism).mor₃ =
      traceAnalyticStableInfinityCategory.cofiberCoconeMap morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

/-- The package-level chosen fiber map composes with the original morphism
to zero. -/
theorem traceAnalyticStableInfinityCategory_fiberMap_comp_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    traceAnalyticStableInfinityCategory_fiberMap morphism ≫ morphism =
      0 :=
  traceAnalyticStableInfinityCategory.fiberMap_comp_morphism morphism

end AnalyticMotives
end LFunctions
end Boundary
