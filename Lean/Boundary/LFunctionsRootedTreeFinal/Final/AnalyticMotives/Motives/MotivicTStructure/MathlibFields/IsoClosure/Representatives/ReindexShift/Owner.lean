import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.ReindexShift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.Owner

/-!
# Reindexed bounded representatives for iso-closed predicates

This file transports shifted bounded representative membership across the
stable reindexing isomorphism which presents an unshifted bounded source object
as a shifted representative of an oppositely shifted bounded complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- An unshifted bounded source object belongs to the iso-closed analytic
aisle at any cut above a chosen reindexing degree. -/
theorem sourceStableWeightBoundedObject_mem_aisleLEIsoClosed_as_degree
    (cut degree : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed
      cut
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex) :=
  let shifted_mem :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed
        cut
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          (complex.shift (-degree))
          degree) :=
    TraceAnalyticMotivicTStructure.aisleLEIsoClosed_of_shiftedBounded
      cut
      (complex.shift (-degree))
      degree
      degree_le
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticMotivicTStructure.aisleLEIsoClosed cut)
    (TraceAnalyticMotiveComparison
      .sourceStableShiftedWeightBoundedObjectReindexIso complex degree)
    shifted_mem

/-- An unshifted bounded source object belongs to the iso-closed analytic
coaisle at any cut below a chosen reindexing degree. -/
theorem sourceStableWeightBoundedObject_mem_coaisleGEIsoClosed_as_degree
    (cut degree : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
      cut
      (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        complex) :=
  let shifted_mem :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
        cut
        (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
          (complex.shift (-degree))
          degree) :=
    TraceAnalyticMotivicTStructure.coaisleGEIsoClosed_of_shiftedBounded
      cut
      (complex.shift (-degree))
      degree
      cut_le
  CategoryTheory.mem_of_iso
    (P := TraceAnalyticMotivicTStructure.coaisleGEIsoClosed cut)
    (TraceAnalyticMotiveComparison
      .sourceStableShiftedWeightBoundedObjectReindexIso complex degree)
    shifted_mem

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
