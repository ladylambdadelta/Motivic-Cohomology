import Mathlib.CategoryTheory.Triangulated.TriangleShift
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Geometry.Owner

/-!
# Shifts of analytic stable motive triangles

This owner file exposes the shift functors on the triangle category of
analytic stable motives and the coherence isomorphisms relating triple
rotation to triangle shift.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The degree-shift functor on analytic stable motive triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor
    (degree : ℤ) :
    TraceAnalyticStableMotiveQuasicategory.triangleCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.Triangle.shiftFunctor
    StableInfinityOwner.PresentedCategory
    degree

/-- The zero-shift isomorphism on analytic stable motive triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleShiftZeroIso :
    TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor 0 ≅
      𝟭 TraceAnalyticStableMotiveQuasicategory.triangleCategory :=
  Pretriangulated.Triangle.shiftFunctorZero
    StableInfinityOwner.PresentedCategory

/-- The additivity isomorphism for shifts of analytic stable motive
triangles. -/
def TraceAnalyticStableMotiveQuasicategory.triangleShiftAddIso
    (left right total : ℤ) (sum : left + right = total) :
    TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor total ≅
      TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor left ⋙
        TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor right :=
  Pretriangulated.Triangle.shiftFunctorAdd'
    StableInfinityOwner.PresentedCategory
    left
    right
    total
    sum

/-- Three rotations of analytic stable motive triangles identify with shift
by `1`. -/
def TraceAnalyticStableMotiveQuasicategory.rotateRotateRotateIso :
    TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor ⋙
        TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor ⋙
          TraceAnalyticStableMotiveQuasicategory.triangleRotateFunctor ≅
      TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor 1 :=
  Pretriangulated.rotateRotateRotateIso
    StableInfinityOwner.PresentedCategory

/-- Three inverse rotations of analytic stable motive triangles identify with
shift by `-1`. -/
def TraceAnalyticStableMotiveQuasicategory.invRotateInvRotateInvRotateIso :
    TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor ⋙
        TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor ⋙
          TraceAnalyticStableMotiveQuasicategory.triangleInvRotateFunctor ≅
      TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor (-1) :=
  Pretriangulated.invRotateInvRotateInvRotateIso
    StableInfinityOwner.PresentedCategory

/-- The triangle-shift functor is Mathlib's triangle shift functor. -/
theorem TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor_eq
    (degree : ℤ) :
    TraceAnalyticStableMotiveQuasicategory.triangleShiftFunctor degree =
      Pretriangulated.Triangle.shiftFunctor
        StableInfinityOwner.PresentedCategory
        degree :=
  rfl

/-- The triple-rotation isomorphism is Mathlib's triple-rotation
isomorphism. -/
theorem TraceAnalyticStableMotiveQuasicategory.rotateRotateRotateIso_eq :
    TraceAnalyticStableMotiveQuasicategory.rotateRotateRotateIso =
      Pretriangulated.rotateRotateRotateIso
        StableInfinityOwner.PresentedCategory :=
  rfl

/-- The triple-inverse-rotation isomorphism is Mathlib's triple-inverse-
rotation isomorphism. -/
theorem
    TraceAnalyticStableMotiveQuasicategory.invRotateInvRotateInvRotateIso_eq :
    TraceAnalyticStableMotiveQuasicategory.invRotateInvRotateInvRotateIso =
      Pretriangulated.invRotateInvRotateInvRotateIso
        StableInfinityOwner.PresentedCategory :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
