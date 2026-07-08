import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Bounds.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Bounds.IsoClosure.Owner

/-!
# Stable bounded representatives for analytic truncations

This file connects the concrete stable truncation vertices to the bounded
comparison-source representatives constructed from the same concrete
truncation complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The stable upper truncation is the stable bounded object represented by
the concrete bounded upper truncation. -/
theorem stableTruncGE_eq_sourceStableWeightBoundedObject
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableTruncGE cut complex.complex =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        (TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
          cut
          complex) :=
  let complex_eq :
      (TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
        cut
        complex).complex =
        TraceAnalyticMotivicTStructure.additiveTruncGE cut complex.complex :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy_complex
      cut
      complex
  Eq.trans
    (TraceAnalyticMotivicTStructure.stableTruncGE_eq_objectOf
      cut
      complex.complex)
    (Eq.symm
      (Eq.trans
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_eq
          (TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
            cut
            complex))
        (Eq.trans
          (congrArg
            TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_eq
              (TraceAnalyticMotivicTStructure.sourceAdditiveTruncGEWeightBoundedBy
                cut
                complex)))
          (congrArg
            (fun additiveComplex =>
              TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  additiveComplex))
            complex_eq))))

/-- The stable lower truncation is the stable bounded object represented by
the concrete bounded lower truncation. -/
theorem stableTruncLE_eq_sourceStableWeightBoundedObject
    (cut : ℤ)
    {bound : Nat}
    (complex :
      TraceAnalyticMotiveComparison.SourceComplexWeightBoundedBy bound)
    [∀ degree, complex.complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableTruncLE cut complex.complex =
      TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject
        (TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
          cut
          complex) :=
  let complex_eq :
      (TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
        cut
        complex).complex =
        TraceAnalyticMotivicTStructure.additiveTruncLE cut complex.complex :=
    TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy_complex
      cut
      complex
  Eq.trans
    (TraceAnalyticMotivicTStructure.stableTruncLE_eq_objectOf
      cut
      complex.complex)
    (Eq.symm
      (Eq.trans
        (TraceAnalyticMotiveComparison.sourceStableWeightBoundedObject_eq
          (TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
            cut
            complex))
        (Eq.trans
          (congrArg
            TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticMotiveComparison.sourceWeightBoundedHomotopyObject_eq
              (TraceAnalyticMotivicTStructure.sourceAdditiveTruncLEWeightBoundedBy
                cut
                complex)))
          (congrArg
            (fun additiveComplex =>
              TraceAnalyticDMgmComparisonSource.objectOf
                (TraceAnalyticAdditiveHomotopyCategory.objectOf
                  additiveComplex))
            complex_eq))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
