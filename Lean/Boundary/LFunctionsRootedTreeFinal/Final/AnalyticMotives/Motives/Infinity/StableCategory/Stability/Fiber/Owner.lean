import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.InvRotation.Owner

/-!
# Fiber triangles in the analytic stable motive category

This owner file exposes the fiber side of stability.  The fiber triangle of a
morphism is the inverse rotation of its chosen cofiber triangle, so the
construction is definitional and uses the already-proved analytic stable
cofiber calculus.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen fiber object of a morphism in the analytic stable motive
category. -/
def TraceAnalyticStableMotiveQuasicategory.fiberObject
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedCategory :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangle morphism).obj₁

/-- The chosen fiber map into the source of a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.fiberMap
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberObject morphism ⟶
      source :=
  (TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangle morphism).mor₁

/-- The chosen fiber triangle of a morphism. -/
def TraceAnalyticStableMotiveQuasicategory.fiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangle morphism

/-- The chosen fiber triangle is distinguished. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  TraceAnalyticStableMotiveQuasicategory
    .invRotatedCofiberTriangle_distinguished morphism

/-- The first object of the chosen fiber triangle is the chosen fiber
object. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_obj₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).obj₁ =
      TraceAnalyticStableMotiveQuasicategory.fiberObject morphism :=
  rfl

/-- The second object of the chosen fiber triangle is the source of the
original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_obj₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).obj₂ =
      source :=
  rfl

/-- The third object of the chosen fiber triangle is the target of the
original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_obj₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).obj₃ =
      target :=
  rfl

/-- The first map of the chosen fiber triangle is the chosen fiber map. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).mor₁ =
      TraceAnalyticStableMotiveQuasicategory.fiberMap morphism :=
  rfl

/-- The second map of the chosen fiber triangle is the original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).mor₂ =
      morphism :=
  rfl

/-- The third map of the chosen fiber triangle is the inverse-rotated
connecting map. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle morphism).mor₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

/-- The chosen fiber map composes with the original morphism to zero. -/
theorem TraceAnalyticStableMotiveQuasicategory.fiberMap_comp_morphism
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.fiberMap morphism ≫
        morphism =
      0 :=
  TraceAnalyticStableMotiveQuasicategory
    .distinguishedTriangle_mor₁_comp_mor₂
    (TraceAnalyticStableMotiveQuasicategory.fiberTriangle morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .fiberTriangle_distinguished morphism)

end AnalyticMotives
end LFunctions
end Boundary
