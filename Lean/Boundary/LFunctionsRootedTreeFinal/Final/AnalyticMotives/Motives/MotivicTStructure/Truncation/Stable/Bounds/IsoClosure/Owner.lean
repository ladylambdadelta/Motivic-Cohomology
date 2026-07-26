import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Stable.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.GE.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.LE.Bounds.IsoClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Bounded.IsoClosure.Owner

/-!
# Stable iso-closure bounded representatives for analytic truncations

This file sends the concrete iso-closure bounded truncation complexes through
the homotopy category and stable Verdier quotient, proving that the stable
truncation vertices are actual degreewise iso-closure bounded stable source
objects.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The stable upper truncation is represented by a concrete degreewise
iso-closure bounded upper truncation complex. -/
theorem stableTruncGE_degreewiseIsoClosureBoundedStableRepresentative
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableRepresentative
        (TraceAnalyticMotivicTStructure.stableTruncGE cut complex) :=
  Exists.intro
    (TraceAnalyticMotivicTStructure.additiveTruncGEIsoClosureBound
      cut
      bound
      complex)
    (Exists.intro
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .additiveTruncGE_sourceComplexDegreewiseIsoClosureBoundedBy
            cut
            complex
            bounded)
        (TraceAnalyticMotivicTStructure.stableTruncGE_eq_objectOf
          cut
          complex)))

/-- The stable upper truncation belongs to the degreewise iso-closure bounded
stable source predicate. -/
theorem stableTruncGE_degreewiseIsoClosureBoundedStableObject
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotivicTStructure.stableTruncGE cut complex) :=
  CategoryTheory.le_isoClosure
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableRepresentative
    (TraceAnalyticMotivicTStructure.stableTruncGE cut complex)
    (TraceAnalyticMotivicTStructure
      .stableTruncGE_degreewiseIsoClosureBoundedStableRepresentative
        cut
        complex
        bounded)

/-- The stable lower truncation is represented by a concrete degreewise
iso-closure bounded lower truncation complex. -/
theorem stableTruncLE_degreewiseIsoClosureBoundedStableRepresentative
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableRepresentative
        (TraceAnalyticMotivicTStructure.stableTruncLE cut complex) :=
  Exists.intro
    (TraceAnalyticMotivicTStructure.additiveTruncLEIsoClosureBound
      cut
      bound
      complex)
    (Exists.intro
      (TraceAnalyticMotivicTStructure.additiveTruncLE cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .additiveTruncLE_sourceComplexDegreewiseIsoClosureBoundedBy
            cut
            complex
            bounded)
        (TraceAnalyticMotivicTStructure.stableTruncLE_eq_objectOf
          cut
          complex)))

/-- The stable lower truncation belongs to the degreewise iso-closure bounded
stable source predicate. -/
theorem stableTruncLE_degreewiseIsoClosureBoundedStableObject
    (cut : ℤ)
    {bound : Nat}
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoClosureBoundedBy
        complex
        bound)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableObject
        (TraceAnalyticMotivicTStructure.stableTruncLE cut complex) :=
  CategoryTheory.le_isoClosure
    TraceAnalyticDMgmComparisonSource
      .degreewiseIsoClosureBoundedStableRepresentative
    (TraceAnalyticMotivicTStructure.stableTruncLE cut complex)
    (TraceAnalyticMotivicTStructure
      .stableTruncLE_degreewiseIsoClosureBoundedStableRepresentative
        cut
        complex
        bounded)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
