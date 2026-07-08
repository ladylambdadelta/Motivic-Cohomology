import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Monotonicity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Shift.Owner

/-!
# Shift fields for bounded stable source predicates

This file proves the bounded-source version of the Mathlib-facing shift
fields.  The shifted object is still displayed as the ambient shifted object,
together with its boundedness proof; this is the canonical input for later
packaging the shift as an endofunctor of the bounded full subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The ambient shift of a bounded stable source object is bounded stable. -/
theorem shifted_object_membership
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.boundedStableObject
      (object.object⟦degree⟧) :=
  TraceAnalyticDMgmComparisonSource.boundedStableObject_shift
    object.membership
    degree

/-- The ambient shift of a bounded stable source object, packaged again as a
bounded stable source object. -/
def shiftedObject
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.BoundedStable where
  obj := object.object⟦degree⟧
  property :=
    TraceAnalyticDMgmComparisonSource.BoundedStable
      .shifted_object_membership object degree

/-- The packaged shifted bounded object has the expected ambient object. -/
theorem shiftedObject_object
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable
      .shiftedObject object degree).object =
      object.object⟦degree⟧ :=
  rfl

/-- Mathlib `LE_shift` field for bounded stable source predicates, displayed
on the ambient shifted object. -/
theorem mathlibLE_shift_ambient
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE n object) :
    TraceAnalyticMotivicTStructure.mathlibLE n' (object.object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.mathlibLE_shift
    n
    a
    n'
    h
    object.object
    membership

/-- Mathlib `LE_shift` field for bounded stable source predicates, displayed
on the packaged shifted bounded object. -/
theorem mathlibLE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE n object) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibLE
      n'
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftedObject object a) :=
  TraceAnalyticDMgmComparisonSource.BoundedStable
    .mathlibLE_shift_ambient
      n
      a
      n'
      h
      object
      membership

/-- Mathlib `GE_shift` field for bounded stable source predicates, displayed
on the ambient shifted object. -/
theorem mathlibGE_shift_ambient
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE n object) :
    TraceAnalyticMotivicTStructure.mathlibGE n' (object.object⟦a⟧) :=
  TraceAnalyticMotivicTStructure.mathlibGE_shift
    n
    a
    n'
    h
    object.object
    membership

/-- Mathlib `GE_shift` field for bounded stable source predicates, displayed
on the packaged shifted bounded object. -/
theorem mathlibGE_shift
    (n a n' : ℤ)
    (h : a + n' = n)
    (object : TraceAnalyticDMgmComparisonSource.BoundedStable)
    (membership :
      TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE n object) :
    TraceAnalyticDMgmComparisonSource.BoundedStable.mathlibGE
      n'
      (TraceAnalyticDMgmComparisonSource.BoundedStable
        .shiftedObject object a) :=
  TraceAnalyticDMgmComparisonSource.BoundedStable
    .mathlibGE_shift_ambient
      n
      a
      n'
      h
      object
      membership

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
