import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner

/-!
# Inverse-rotated cofiber triangles in the analytic stable motive category

This owner file exposes the inverse rotation of the chosen cofiber triangle
attached to a morphism and proves that the inverse-rotated triangle is
distinguished.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The inverse-rotated cofiber triangle attached to a morphism in the
analytic stable motive category. -/
def TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberTriangle morphism).invRotate

/-- The inverse-rotated cofiber triangle is the inverse-rotation functor
applied to the chosen cofiber triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle_eq
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
        morphism =
      TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor.obj
        (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
          morphism) :=
  rfl

/-- The inverse-rotated cofiber triangle is distinguished. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle
        morphism ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.inv_rot_of_distTriang
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
      morphism)
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism)

/-- The first map of the inverse-rotated cofiber triangle is the shifted
negative boundary followed by the unit comparison. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism).mor₁ =
      -((TraceAnalyticStableMotiveQuasicategory
        .cofiberBoundary morphism)⟦(-1 : ℤ)⟧') ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).unitIso.inv.app _ :=
  rfl

/-- The second map of the inverse-rotated cofiber triangle is the original
morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism).mor₂ =
      morphism :=
  rfl

/-- The third map of the inverse-rotated cofiber triangle is the chosen
cofiber cocone map followed by the counit comparison. -/
theorem TraceAnalyticStableMotiveQuasicategory.invRotatedCofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .invRotatedCofiberTriangle morphism).mor₃ =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap
          morphism ≫
        (shiftEquiv StableInfinityOwner.PresentedCategory
          (1 : ℤ)).counitIso.inv.app _ :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
