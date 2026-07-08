import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Cofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner

/-!
# Rotated cofiber triangles in the analytic stable motive category

This owner file exposes the rotation of the chosen cofiber triangle attached
to a morphism and proves that the rotated triangle is distinguished.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated cofiber triangle attached to a morphism in the analytic stable
motive category. -/
def TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    StableInfinityOwner.PresentedTriangle :=
  (TraceAnalyticStableMotiveQuasicategory
    .cofiberTriangle morphism).rotate

/-- The rotated cofiber triangle is the rotation functor applied to the chosen
cofiber triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle_eq
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
        morphism =
      TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor.obj
        (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
          morphism) :=
  rfl

/-- The rotated cofiber triangle is distinguished. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle_distinguished
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle
        morphism ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  (TraceAnalyticStableMotiveQuasicategory.rotate_distinguishedTriangle
    (TraceAnalyticStableMotiveQuasicategory.cofiberTriangle
      morphism)).1
    (TraceAnalyticStableMotiveQuasicategory
      .cofiberTriangle_distinguished morphism)

/-- The first map of the rotated cofiber triangle is the chosen cofiber
cocone map. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle_mor₁
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism).mor₁ =
      TraceAnalyticStableMotiveQuasicategory.cofiberCoconeMap morphism :=
  rfl

/-- The second map of the rotated cofiber triangle is the chosen cofiber
boundary map. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle_mor₂
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism).mor₂ =
      TraceAnalyticStableMotiveQuasicategory.cofiberBoundary morphism :=
  rfl

/-- The third map of the rotated cofiber triangle is the shifted negative of
the original morphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotatedCofiberTriangle_mor₃
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    (TraceAnalyticStableMotiveQuasicategory
      .rotatedCofiberTriangle morphism).mor₃ =
      -morphism⟦(1 : ℤ)⟧' :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
