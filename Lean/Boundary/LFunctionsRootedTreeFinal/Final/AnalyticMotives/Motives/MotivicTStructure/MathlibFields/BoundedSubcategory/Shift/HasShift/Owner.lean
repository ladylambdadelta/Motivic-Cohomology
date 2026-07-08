import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.Functor.Inclusion.Owner

/-!
# The bounded stable source has coherent shifts

The bounded stable source is a full subcategory of the ambient analytic
comparison source, and the bounded shift functors commute with the inclusion.
This file uses Mathlib's fully faithful induced-shift construction to package
those restricted shifts as a genuine coherent `HasShift` structure.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The bounded stable source inherits coherent integer shifts from the
ambient analytic comparison source through its fully faithful inclusion. -/
def hasShift :
    HasShift TraceAnalyticDMgmComparisonSource.BoundedStable ℤ :=
  (CategoryTheory.fullyFaithfulFullSubcategoryInclusion
    TraceAnalyticDMgmComparisonSource.boundedStableObject).hasShift
      (fun degree =>
        TraceAnalyticDMgmComparisonSource.BoundedStable
          .shiftFunctor degree)
      (fun degree =>
        eqToIso
          (TraceAnalyticDMgmComparisonSource.BoundedStable
            .shiftFunctor_comp_inclusion degree))

/-- The bounded stable source uses the induced coherent integer shifts as its
Mathlib shift instance. -/
instance instHasShift :
    HasShift TraceAnalyticDMgmComparisonSource.BoundedStable ℤ :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.hasShift

/-- The Mathlib shift functor for the bounded stable source is the bounded
shift functor constructed from ambient analytic shifts. -/
theorem mathlib_shiftFunctor_eq_boundedShiftFunctor
    (degree : ℤ) :
    CategoryTheory.shiftFunctor
        TraceAnalyticDMgmComparisonSource.BoundedStable degree =
      TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree :=
  rfl

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
