import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.BoundedSubcategory.Shift.HasShift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Shift.Owner

/-!
# Additivity of bounded stable shifts

The ambient analytic comparison source has additive integer shifts.  Since the
bounded stable source is a full subcategory and its shift functors commute with
the faithful inclusion, bounded shifts are additive as well.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace BoundedStable

/-- The concrete bounded shift functor is additive. -/
def shiftFunctorAdditive
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
      .Additive :=
  letI ambientAdditive :
      (CategoryTheory.shiftFunctor
        TraceAnalyticDMgmComparisonSource degree).Additive :=
    TraceAnalyticDMgmComparisonSource.shiftFunctorAdditive degree
  CategoryTheory.Functor.additive_of_comp_faithful
    (TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctor degree)
    TraceAnalyticDMgmComparisonSource.BoundedStable.inclusion

/-- Mathlib's induced bounded shift functor is additive. -/
instance instMathlibShiftFunctorAdditive
    (degree : ℤ) :
    (CategoryTheory.shiftFunctor
      TraceAnalyticDMgmComparisonSource.BoundedStable degree).Additive :=
  TraceAnalyticDMgmComparisonSource.BoundedStable.shiftFunctorAdditive degree

end BoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
