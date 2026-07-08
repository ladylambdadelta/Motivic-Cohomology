import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Shift.Owner

/-!
# Categorical shifts of stable shifted bounded source objects

This file relates the representative degree shift used by bounded analytic
source objects to the categorical shift in the stable analytic Verdier
quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Raising the representative degree by `shift` gives an object isomorphic to
the categorical shift by `shift` of the original stable representative. -/
def TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectAddRightIso
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree shift : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        (degree + shift) ≅
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree)⟦shift⟧ :=
  TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
      ((CategoryTheory.shiftFunctorAdd'
        TraceAnalyticAdditiveHomotopyCategory
        degree
        shift
        (degree + shift)
        rfl).app
        (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
          complex)) ≪≫
    TraceAnalyticStableMotiveCategory.objectOfShiftIso
      (TraceAnalyticMotiveComparison.sourceShiftedWeightBoundedHomotopyObject
        complex
        degree)
      shift

end AnalyticMotives
end LFunctions
end Boundary
