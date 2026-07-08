import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Weights.Source.Bounds.Stable.Owner

/-!
# Analytic motivic aisle and coaisle predicates

This file defines the first concrete aisle and coaisle membership predicates
for the analytic motivic t-structure lane.  Membership is witnessed by an
actual shifted bounded analytic representative in the stable comparison source,
together with the relevant integer degree inequality.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Analytic motivic nonpositive aisle at the cut `cut`: objects represented
by shifted bounded analytic complexes in degrees at most `cut`. -/
def TraceAnalyticMotivicTStructure.aisleLE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  ∃ (bound : Nat),
    ∃ (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
    ∃ (degree : ℤ),
      degree ≤ cut ∧
        object =
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            complex
            degree

/-- Analytic motivic nonnegative coaisle at the cut `cut`: objects represented
by shifted bounded analytic complexes in degrees at least `cut`. -/
def TraceAnalyticMotivicTStructure.coaisleGE
    (cut : ℤ)
    (object : TraceAnalyticDMgmComparisonSource) :
    Prop :=
  ∃ (bound : Nat),
    ∃ (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound),
    ∃ (degree : ℤ),
      cut ≤ degree ∧
        object =
          TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
            complex
            degree

/-- A shifted bounded stable representative in degree at most `cut` belongs to
the analytic motivic aisle at `cut`. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (degree_le : degree ≤ cut) :
    TraceAnalyticMotivicTStructure.aisleLE
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  Exists.intro
    bound
    (Exists.intro
      complex
      (Exists.intro
        degree
        (And.intro
          degree_le
          rfl)))

/-- A shifted bounded stable representative in degree at least `cut` belongs to
the analytic motivic coaisle at `cut`. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    (degree : ℤ)
    (cut_le : cut ≤ degree) :
    TraceAnalyticMotivicTStructure.coaisleGE
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        degree) :=
  Exists.intro
    bound
    (Exists.intro
      complex
      (Exists.intro
        degree
        (And.intro
          cut_le
          rfl)))

/-- An unshifted bounded stable representative belongs to the aisle at any
nonnegative cut. -/
theorem TraceAnalyticMotivicTStructure.aisleLE_of_bounded
    (cut : ℤ)
    (zero_le_cut : (0 : ℤ) ≤ cut)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.aisleLE
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        0) :=
  TraceAnalyticMotivicTStructure.aisleLE_of_shiftedBounded
    cut
    complex
    0
    zero_le_cut

/-- An unshifted bounded stable representative belongs to the coaisle at any
nonpositive cut. -/
theorem TraceAnalyticMotivicTStructure.coaisleGE_of_bounded
    (cut : ℤ)
    (cut_le_zero : cut ≤ (0 : ℤ))
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound) :
    TraceAnalyticMotivicTStructure.coaisleGE
      cut
      (TraceAnalyticMotiveComparison.sourceStableShiftedWeightBoundedObject
        complex
        0) :=
  TraceAnalyticMotivicTStructure.coaisleGE_of_shiftedBounded
    cut
    complex
    0
    cut_le_zero

end AnalyticMotives
end LFunctions
end Boundary
