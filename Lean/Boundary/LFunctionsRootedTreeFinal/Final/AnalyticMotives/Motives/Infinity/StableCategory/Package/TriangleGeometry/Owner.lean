import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level triangle geometry

This owner file identifies the triangle projection and rotation functors in
the assembled analytic stable-infinity package with Mathlib's triangle
geometry functors.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level first triangle projection is Mathlib's first triangle
projection. -/
theorem traceAnalyticStableInfinityCategory_triangleFirstProjection_eq :
    traceAnalyticStableInfinityCategory.triangleFirstProjection =
      Pretriangulated.Triangle.π₁ :=
  rfl

/-- The package-level second triangle projection is Mathlib's second triangle
projection. -/
theorem traceAnalyticStableInfinityCategory_triangleSecondProjection_eq :
    traceAnalyticStableInfinityCategory.triangleSecondProjection =
      Pretriangulated.Triangle.π₂ :=
  rfl

/-- The package-level third triangle projection is Mathlib's third triangle
projection. -/
theorem traceAnalyticStableInfinityCategory_triangleThirdProjection_eq :
    traceAnalyticStableInfinityCategory.triangleThirdProjection =
      Pretriangulated.Triangle.π₃ :=
  rfl

/-- The package-level triangle-rotation functor is Mathlib's rotation
functor. -/
theorem traceAnalyticStableInfinityCategory_triangleRotateFunctor_eq :
    traceAnalyticStableInfinityCategory.triangleRotateFunctor =
      Pretriangulated.rotate StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level inverse triangle-rotation functor is Mathlib's
inverse-rotation functor. -/
theorem traceAnalyticStableInfinityCategory_triangleInvRotateFunctor_eq :
    traceAnalyticStableInfinityCategory.triangleInvRotateFunctor =
      Pretriangulated.invRotate StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level triangle-rotation equivalence is Mathlib's
triangle-rotation equivalence. -/
theorem traceAnalyticStableInfinityCategory_triangleRotationEquivalence_eq :
    traceAnalyticStableInfinityCategory.triangleRotationEquivalence =
      Pretriangulated.triangleRotation StableInfinityOwner.PresentedCategory :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
