import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Package-level triangle shifts

This owner file exposes the triangle-shift and triple-rotation coherence
isomorphisms through the assembled analytic stable-infinity package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level triangle shift functor is Mathlib's triangle shift
functor. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftFunctor_eq
    (degree : ℤ) :
    traceAnalyticStableInfinityCategory.triangleShiftFunctor degree =
      Pretriangulated.Triangle.shiftFunctor
        StableInfinityOwner.PresentedCategory
        degree :=
  rfl

/-- The package-level triple-rotation isomorphism is Mathlib's
triple-rotation isomorphism. -/
theorem traceAnalyticStableInfinityCategory_rotateRotateRotateIso_eq :
    traceAnalyticStableInfinityCategory.rotateRotateRotateIso =
      Pretriangulated.rotateRotateRotateIso
        StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level triple-inverse-rotation isomorphism is Mathlib's
triple-inverse-rotation isomorphism. -/
theorem
    traceAnalyticStableInfinityCategory_invRotateInvRotateInvRotateIso_eq :
    traceAnalyticStableInfinityCategory.invRotateInvRotateInvRotateIso =
      Pretriangulated.invRotateInvRotateInvRotateIso
        StableInfinityOwner.PresentedCategory :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
