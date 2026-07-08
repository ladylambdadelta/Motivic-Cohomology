import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StablePresentation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.FiberCofiber.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Shift.Owner

/-!
# Stability facts for the analytic stable motive category

This owner file exposes the concrete stability data supplied by the
Verdier-localized analytic motive category: suspension, loop,
suspension-loop equivalence, cofiber triangles, contractible distinguished
triangles, rotation closure, and completion of morphisms between distinguished
triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace StableInfinityOwner

abbrev PresentedCategory :=
  TraceAnalyticStableMotiveQuasicategory.presentedCategory

abbrev PresentedTriangle :=
  Pretriangulated.Triangle PresentedCategory

end StableInfinityOwner

/-- The suspension functor in the analytic stable motive category is the
positive unit shift on the Verdier quotient. -/
def TraceAnalyticStableMotiveQuasicategory.suspensionFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  shiftFunctor StableInfinityOwner.PresentedCategory (1 : ℤ)

/-- The loop functor in the analytic stable motive category is the negative
unit shift on the Verdier quotient. -/
def TraceAnalyticStableMotiveQuasicategory.loopFunctor :
    StableInfinityOwner.PresentedCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  shiftFunctor StableInfinityOwner.PresentedCategory (-1 : ℤ)

/-- Suspension and loop form the unit-shift equivalence on the analytic stable
motive category. -/
def TraceAnalyticStableMotiveQuasicategory.suspensionLoopEquivalence :
    StableInfinityOwner.PresentedCategory ≌
      StableInfinityOwner.PresentedCategory :=
  shiftEquiv StableInfinityOwner.PresentedCategory (1 : ℤ)

/-- Every morphism in the presented analytic stable motive category has a
distinguished cofiber triangle. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguishedCofiberTriangle
    {source target : StableInfinityOwner.PresentedCategory}
    (morphism : source ⟶ target) :
    ∃ (cofiber : StableInfinityOwner.PresentedCategory)
      (coconeMap : target ⟶ cofiber)
      (boundary : cofiber ⟶ source⟦(1 : ℤ)⟧),
      Pretriangulated.Triangle.mk morphism coconeMap boundary ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.distinguished_cocone_triangle morphism

/-- Contractible triangles are distinguished in the presented analytic stable
motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory.contractibleTriangle_distinguished
    (object : StableInfinityOwner.PresentedCategory) :
    Pretriangulated.contractibleTriangle object ∈
      TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.contractible_distinguished object

/-- Distinguished triangles are closed under rotation in the presented
analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotate_distinguishedTriangle
    (triangle : StableInfinityOwner.PresentedTriangle) :
    triangle ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles ↔
      triangle.rotate ∈
        TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :=
  Pretriangulated.rotate_distinguished_triangle triangle

/-- A morphism of the first two vertices of distinguished triangles extends to
the third vertex in the presented analytic stable motive category. -/
theorem TraceAnalyticStableMotiveQuasicategory.complete_distinguishedTriangleMorphism
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    ∃ map₃ : first.obj₃ ⟶ second.obj₃,
      first.mor₂ ≫ map₃ = map₂ ≫ second.mor₂ ∧
        first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' = map₃ ≫ second.mor₃ :=
  Pretriangulated.complete_distinguished_triangle_morphism
    first
    second
    first_distinguished
    second_distinguished
    map₁
    map₂
    square

end AnalyticMotives
end LFunctions
end Boundary
