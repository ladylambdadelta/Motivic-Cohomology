import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Bounds.Membership.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.IsoClosure.Representatives.ReindexShift.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.MathlibFields.Reindexed.Owner

/-!
# Mathlib-facing membership for stable bounded truncation vertices

This file reindexes the zero-cut concrete iso-closed membership facts for
stable bounded truncation vertices into the Mathlib-facing predicates.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The stable upper truncation of a bounded complex belongs to the
Mathlib-facing `LE 0` predicate. -/
theorem stableTruncGE_mem_mathlibLE_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.mathlibLE
      0
      (TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex) :=
  TraceAnalyticMotivicTStructure.stableTruncGE_mem_coaisleGEIsoClosed_zero
    cut
    complex

/-- The stable lower truncation of a bounded complex belongs to the
Mathlib-facing `GE 0` predicate. -/
theorem stableTruncLE_mem_mathlibGE_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.mathlibGE
      0
      (TraceAnalyticMotivicTStructure.stableTruncLE cut complex.complex) :=
  TraceAnalyticMotivicTStructure.stableTruncLE_mem_aisleLEIsoClosed_zero
    cut
    complex

/-- The stable lower truncation of a bounded complex belongs to the
Mathlib-facing `LE 0` predicate. -/
theorem stableTruncLE_mem_mathlibLE_zero
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.mathlibLE
      0
      (TraceAnalyticMotivicTStructure.stableTruncLE cut complex.complex) :=
  let boundedTrunc :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        (TraceAnalyticMotivicTStructure.additiveTruncLEBound cut complex) :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
      cut
      complex
  let bounded_mem :
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed
        0
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          boundedTrunc) :=
    TraceAnalyticMotivicTStructure
      .sourceStableWeightBoundedObject_mem_coaisleGEIsoClosed_as_degree
        0
        0
        boundedTrunc
        le_rfl
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.coaisleGEIsoClosed 0 object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure.stableTruncLE_eq_sourceStableWeightBoundedObject
        cut
        complex))
    bounded_mem

/-- The stable upper truncation of a bounded complex belongs to the
Mathlib-facing `GE 1` predicate. -/
theorem stableTruncGE_mem_mathlibGE_one
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.mathlibGE
      1
      (TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex) :=
  let boundedTrunc :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy
        (TraceAnalyticMotivicTStructure.additiveTruncGEBound cut complex) :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
      cut
      complex
  let bounded_mem :
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed
        (-1)
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
          boundedTrunc) :=
    TraceAnalyticMotivicTStructure
      .sourceStableWeightBoundedObject_mem_aisleLEIsoClosed_as_degree
        (-1)
        (-1)
        boundedTrunc
        le_rfl
  Eq.subst
    (motive := fun object =>
      TraceAnalyticMotivicTStructure.aisleLEIsoClosed (-1) object)
    (Eq.symm
      (TraceAnalyticMotivicTStructure.stableTruncGE_eq_sourceStableWeightBoundedObject
        cut
        complex))
    bounded_mem

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
