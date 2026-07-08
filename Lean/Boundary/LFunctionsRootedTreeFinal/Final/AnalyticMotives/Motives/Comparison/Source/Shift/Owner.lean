import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Shift.Owner

/-!
# Shifts in the analytic comparison source

The analytic comparison source is the stable analytic Verdier quotient.  This
file exposes quotient-functor shift commutation, additivity of integer shifts,
and the represented-object shift isomorphism under comparison-source names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The comparison-source quotient functor commutes with integer shifts. -/
def TraceAnalyticDMgmComparisonSource.quotientFunctorCommShift :
    TraceAnalyticDMgmComparisonSource.quotientFunctor.CommShift ℤ :=
  TraceAnalyticStableMotiveCategory.quotientFunctorCommShift

/-- The comparison-source quotient-functor commutation isomorphism for integer
shifts. -/
def TraceAnalyticDMgmComparisonSource.quotientFunctorCommShiftIso
    (degree : ℤ) :
    CategoryTheory.shiftFunctor
          TraceAnalyticAdditiveHomotopyCategory
          degree ⋙
        TraceAnalyticDMgmComparisonSource.quotientFunctor ≅
      TraceAnalyticDMgmComparisonSource.quotientFunctor ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticDMgmComparisonSource
          degree :=
  TraceAnalyticStableMotiveCategory.quotientFunctorCommShiftIso degree

/-- Comparison-source integer shifts are additive functors. -/
def TraceAnalyticDMgmComparisonSource.shiftFunctorAdditive
    (degree : ℤ) :
    (CategoryTheory.shiftFunctor
      TraceAnalyticDMgmComparisonSource
      degree).Additive :=
  TraceAnalyticStableMotiveCategory.shiftFunctorAdditive degree

/-- The quotient image of a shifted additive homotopy object is isomorphic to
the categorical shift of its comparison-source quotient image. -/
def TraceAnalyticDMgmComparisonSource.objectOfShiftIso
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.objectOf (object⟦degree⟧) ≅
      (TraceAnalyticDMgmComparisonSource.objectOf object)⟦degree⟧ :=
  TraceAnalyticStableMotiveCategory.objectOfShiftIso object degree

/-- The comparison-source object-level quotient shift isomorphism is the stable
analytic quotient shift isomorphism. -/
theorem TraceAnalyticDMgmComparisonSource.objectOfShiftIso_eq_stable
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticDMgmComparisonSource.objectOfShiftIso object degree =
      TraceAnalyticStableMotiveCategory.objectOfShiftIso object degree :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
