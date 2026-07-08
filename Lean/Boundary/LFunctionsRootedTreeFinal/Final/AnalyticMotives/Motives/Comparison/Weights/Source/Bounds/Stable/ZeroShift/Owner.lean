import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Shift.Owner

/-!
# Zero shifts of stable bounded source objects

This file records the canonical stable isomorphism between an unshifted
bounded source object and the same bounded source object viewed as a
degree-zero shifted representative.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The degree-zero shifted bounded stable object is canonically isomorphic to
the unshifted bounded stable object. -/
def TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectZeroIso
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        0 ≅
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject complex :=
  TraceAnalyticStableMotiveCategory.objectOfShiftIso
      (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
        complex)
      0 ≪≫
    (CategoryTheory.shiftFunctorZero
      TraceAnalyticStableMotiveCategory
      ℤ).app
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex)

/-- The zero-shift stable comparison is the quotient shift-commutation
isomorphism followed by the stable zero-shift isomorphism. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectZeroIso_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectZeroIso
        complex =
      TraceAnalyticStableMotiveCategory.objectOfShiftIso
          (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject
            complex)
          0 ≪≫
        (CategoryTheory.shiftFunctorZero
          TraceAnalyticStableMotiveCategory
          ℤ).app
          (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
            complex) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
