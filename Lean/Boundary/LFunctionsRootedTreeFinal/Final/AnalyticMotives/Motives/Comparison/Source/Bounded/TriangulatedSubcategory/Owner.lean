import Mathlib.CategoryTheory.Triangulated.Subcategory
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Zero.Owner

/-!
# Bounded stable predicate as triangulated-subcategory input

This file records the already-proved zero and shift fields for the
bounded-stable comparison-source predicate in exactly the shape required by
Mathlib's `Triangulated.Subcategory` constructor.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticDMgmComparisonSource

/-- The bounded-stable comparison-source predicate contains a zero object in
the ambient analytic comparison source. -/
theorem boundedStableObject_triangulatedSubcategory_zero' :
    ∃ (zeroObject : TraceAnalyticDMgmComparisonSource)
      (_ : IsZero zeroObject),
      TraceAnalyticDMgmComparisonSource.boundedStableObject zeroObject :=
  Exists.intro
    TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject.object
    (Exists.intro
      TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject_ambient_isZero
      TraceAnalyticDMgmComparisonSource.BoundedStable.zeroObject.membership)

/-- The bounded-stable comparison-source predicate is closed under ambient
integer shifts. -/
theorem boundedStableObject_triangulatedSubcategory_shift
    (object : TraceAnalyticDMgmComparisonSource)
    (degree : ℤ)
    (membership :
      TraceAnalyticDMgmComparisonSource.boundedStableObject object) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (object⟦degree⟧) :=
  TraceAnalyticDMgmComparisonSource.boundedStableObject_shift
    membership
    degree

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
