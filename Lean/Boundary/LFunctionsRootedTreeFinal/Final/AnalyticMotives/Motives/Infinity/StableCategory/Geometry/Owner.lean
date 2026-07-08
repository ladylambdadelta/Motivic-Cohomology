import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Stability.Owner

/-!
# Triangle geometry for the analytic stable motive category

This owner file exposes the triangle-category geometry attached to the
Verdier-localized analytic stable motive category: the three vertex
projections, rotation, inverse rotation, and the rotation autoequivalence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The category of triangles in the presented analytic stable motive
category. -/
abbrev TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.Triangle StableInfinityOwner.PresentedCategory

/-- The first-vertex projection from analytic stable motive triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  Pretriangulated.Triangle.π₁

/-- The second-vertex projection from analytic stable motive triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  Pretriangulated.Triangle.π₂

/-- The third-vertex projection from analytic stable motive triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      StableInfinityOwner.PresentedCategory :=
  Pretriangulated.Triangle.π₃

/-- Rotation as an endofunctor of the analytic stable motive triangle
category. -/
def TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.rotate StableInfinityOwner.PresentedCategory

/-- Inverse rotation as an endofunctor of the analytic stable motive triangle
category. -/
def TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.invRotate StableInfinityOwner.PresentedCategory

/-- Rotation is an autoequivalence of the analytic stable motive triangle
category. -/
def TraceAnalyticStableMotiveQuasicategory.triangleRotationEquivalence :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ≌
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.triangleRotation StableInfinityOwner.PresentedCategory

/-- The first projection is Mathlib's first triangle projection. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleFirstProjection =
      Pretriangulated.Triangle.π₁ :=
  rfl

/-- The second projection is Mathlib's second triangle projection. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleSecondProjection =
      Pretriangulated.Triangle.π₂ :=
  rfl

/-- The third projection is Mathlib's third triangle projection. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleThirdProjection =
      Pretriangulated.Triangle.π₃ :=
  rfl

/-- The triangle-rotation functor is Mathlib's rotation functor. -/
theorem TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor =
      Pretriangulated.rotate StableInfinityOwner.PresentedCategory :=
  rfl

/-- The inverse triangle-rotation functor is Mathlib's inverse-rotation
functor. -/
theorem TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor =
      Pretriangulated.invRotate StableInfinityOwner.PresentedCategory :=
  rfl

/-- The triangle-rotation equivalence is Mathlib's triangle-rotation
autoequivalence. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.triangleRotationEquivalence_eq :
    TraceAnalyticStableMotiveQuasicategory.triangleRotationEquivalence =
      Pretriangulated.triangleRotation StableInfinityOwner.PresentedCategory :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
