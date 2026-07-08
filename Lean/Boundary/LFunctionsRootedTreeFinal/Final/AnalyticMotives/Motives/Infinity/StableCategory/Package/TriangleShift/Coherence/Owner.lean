import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Package.TriangleShift.Owner

/-!
# Package-level triangle-shift coherence

This owner file identifies the zero-shift and additivity isomorphisms for
analytic stable motive triangle shifts with Mathlib's pretriangulated
triangle-shift coherence isomorphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The package-level zero-shift isomorphism for analytic stable motive
triangles is Mathlib's triangle zero-shift isomorphism. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftZeroIso_eq :
    traceAnalyticStableInfinityCategory.triangleShiftZeroIso =
      Pretriangulated.Triangle.shiftFunctorZero
        StableInfinityOwner.PresentedCategory :=
  rfl

/-- The package-level additivity isomorphism for analytic stable motive
triangle shifts is Mathlib's triangle shift-additivity isomorphism. -/
theorem traceAnalyticStableInfinityCategory_triangleShiftAddIso_eq
    (left right total : ℤ) (sum : left + right = total) :
    traceAnalyticStableInfinityCategory.triangleShiftAddIso
        left
        right
        total
        sum =
      Pretriangulated.Triangle.shiftFunctorAdd'
        StableInfinityOwner.PresentedCategory
        left
        right
        total
        sum :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
