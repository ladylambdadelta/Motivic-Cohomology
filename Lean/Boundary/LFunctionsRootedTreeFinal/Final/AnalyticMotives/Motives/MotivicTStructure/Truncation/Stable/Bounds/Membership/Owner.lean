import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.ZeroShift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Bounds.Owner

/-!
# Iso-closed membership for stable bounded truncation vertices

This file turns the concrete bounded upper and lower truncation representatives
into zero-cut iso-closed aisle/coaisle membership facts for the corresponding
stable truncation vertices.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The stable upper truncation of a bounded complex belongs to the zero-cut
iso-closed concrete coaisle. -/
theorem stableTruncGE_mem_coaisleGEIsoClosed_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      0
      (TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex) :=
  let boundedTrunc :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        (TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex) :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
      cut
      complex
  let shifted_mem :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
        0
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          boundedTrunc
          0) :=
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded_self
      boundedTrunc
      0
  let bounded_mem :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
        0
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          boundedTrunc) :=
    CategoryTheory.mem_of_iso
      (P := TraceAnalyticMotivicTStructure.coaisleGEIsoClosed 0)
      (TraceAnalyticMotiveComparison
        .sourceStableShiftedWeightBoundedObjectZeroIso boundedTrunc)
      shifted_mem
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed 0 object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure.stableTruncGE_eq_sourceStableWeightBoundedObject
        cut
        complex))
    bounded_mem

/-- The stable lower truncation of a bounded complex belongs to the zero-cut
iso-closed concrete aisle. -/
theorem stableTruncLE_mem_aisleLEIsoClosed_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      0
      (TraceAnalyticMotivicTStructure.stableTruncLE cut complex.complex) :=
  let boundedTrunc :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        (TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex) :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
      cut
      complex
  let shifted_mem :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed
        0
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          boundedTrunc
          0) :=
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded_self
      boundedTrunc
      0
  let bounded_mem :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed
        0
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          boundedTrunc) :=
    CategoryTheory.mem_of_iso
      (P := TraceAnalyticMotivicTStructure.aisleLEIsoClosed 0)
      (TraceAnalyticMotiveComparison
        .sourceStableShiftedWeightBoundedObjectZeroIso boundedTrunc)
      shifted_mem
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed 0 object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure.stableTruncLE_eq_sourceStableWeightBoundedObject
        cut
        complex))
    bounded_mem

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
