import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.DegreewiseBoundedSubcategory.Shift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Shift.Owner

/-!
# Additivity of degreewise bounded shifts

The ambient analytic comparison source has additive integer shifts.  Since the
degreewise bounded stable source is a full subcategory and its shift functors
commute with the faithful inclusion, degreewise bounded shifts are additive.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource
namespace DegreewiseBoundedStable

/-- The concrete degreewise bounded shift functor is additive. -/
def shiftFunctorAdditive
    (degree : ℤ) :
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shiftFunctor degree).Additive :=
  letI ambientAdditive :
      (CategoryTheory.shiftFunctor
        TraceAnalyticDMgmComparisonSource degree).Additive :=
    TraceAnalyticDMgmComparisonSource.shiftFunctorAdditive degree
  CategoryTheory.Functor.additive_of_comp_faithful
    (TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      .shiftFunctor degree)
    TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable.inclusion

/-- Mathlib's induced degreewise bounded shift functor is additive. -/
instance instMathlibShiftFunctorAdditive
    (degree : ℤ) :
    (CategoryTheory.shiftFunctor
      TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
      degree).Additive :=
  TraceAnalyticDMgmComparisonSource.DegreewiseBoundedStable
    .shiftFunctorAdditive degree

end DegreewiseBoundedStable
end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
