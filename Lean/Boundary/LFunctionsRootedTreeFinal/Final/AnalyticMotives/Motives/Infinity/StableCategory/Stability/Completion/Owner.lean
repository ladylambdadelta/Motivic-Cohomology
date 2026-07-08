import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner

/-!
# Completion of morphisms between distinguished analytic stable triangles

This owner file chooses the third-vertex map supplied by the pretriangulated
completion theorem for a commutative square between distinguished analytic
stable triangles.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The chosen third-vertex map completing a morphism between distinguished
analytic stable triangles. -/
def TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    first.obj₃ ⟶ second.obj₃ :=
  Classical.choose
    (TraceAnalyticStableMotiveQuasicategory
      .complete_distinguishedTriangleMorphism
      first
      second
      first_distinguished
      second_distinguished
      map₁
      map₂
      square)

/-- The chosen third-vertex map satisfies the second-square compatibility. -/
theorem TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₂
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    first.mor₂ ≫
        TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
          first
          second
          first_distinguished
          second_distinguished
          map₁
          map₂
          square =
      map₂ ≫ second.mor₂ :=
  (Classical.choose_spec
    (TraceAnalyticStableMotiveQuasicategory
      .complete_distinguishedTriangleMorphism
      first
      second
      first_distinguished
      second_distinguished
      map₁
      map₂
      square)).1

/-- The chosen third-vertex map satisfies the boundary-square compatibility. -/
theorem TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃_mor₃
    (first second : StableInfinityOwner.PresentedTriangle)
    (first_distinguished :
      first ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (second_distinguished :
      second ∈ TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles)
    (map₁ : first.obj₁ ⟶ second.obj₁)
    (map₂ : first.obj₂ ⟶ second.obj₂)
    (square : first.mor₁ ≫ map₂ = map₁ ≫ second.mor₁) :
    first.mor₃ ≫ map₁⟦(1 : ℤ)⟧' =
      TraceAnalyticStableMotiveQuasicategory.completedTriangleMap₃
          first
          second
          first_distinguished
          second_distinguished
          map₁
          map₂
          square ≫
        second.mor₃ :=
  (Classical.choose_spec
    (TraceAnalyticStableMotiveQuasicategory
      .complete_distinguishedTriangleMorphism
      first
      second
      first_distinguished
      second_distinguished
      map₁
      map₂
      square)).2

end AnalyticMotives
end LFunctions
end Boundary
