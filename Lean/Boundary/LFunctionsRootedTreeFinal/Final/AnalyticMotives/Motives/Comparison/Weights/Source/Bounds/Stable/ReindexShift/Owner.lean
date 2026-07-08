import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Shift.Coherence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Shift.Representatives.Owner

/-!
# Reindexing stable bounded source objects by shifted representatives

This file constructs the canonical isomorphism which presents an unshifted
stable bounded source object as a shifted stable bounded representative at any
chosen integer degree, after shifting the bounded complex in the opposite
direction.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A bounded stable object represented by `complex` is isomorphic to the
degree-`degree` shifted representative of the oppositely shifted bounded
complex. -/
def TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectReindexIso
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        (complex.shift (-degree))
        degree ≅
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject complex :=
  TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
      (TraceAnalyticAdditiveHomotopyCategory
        .shiftedWeightBoundedObjectRepresentativeIso
          (complex.shift (-degree))
          degree).symm ≪≫
    TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
      (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
        ((complex.shiftAddIso (-degree) degree).symm ≪≫
          eqToIso
            (congrArg
              (fun shift => (complex.shift shift).complex)
              (neg_add_cancel degree)) ≪≫
          complex.shiftZeroIso))

/-- The reindexing isomorphism is the quotient image of the representative
comparison followed by the zero-shift coherence isomorphism. -/
theorem TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectReindexIso_eq
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObjectReindexIso
        complex
        degree =
      TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
          (TraceAnalyticAdditiveHomotopyCategory
            .shiftedWeightBoundedObjectRepresentativeIso
              (complex.shift (-degree))
              degree).symm ≪≫
        TraceAnalyticStableMotiveCategory.quotientFunctor.mapIso
          (TraceAnalyticAdditiveHomotopyCategory.quotientFunctor.mapIso
            ((complex.shiftAddIso (-degree) degree).symm ≪≫
              eqToIso
                (congrArg
                  (fun shift => (complex.shift shift).complex)
                  (neg_add_cancel degree)) ≪≫
              complex.shiftZeroIso)) :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
