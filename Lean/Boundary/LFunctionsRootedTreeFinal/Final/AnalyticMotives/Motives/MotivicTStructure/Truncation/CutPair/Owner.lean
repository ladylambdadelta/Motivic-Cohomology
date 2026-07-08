import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Complexes.Owner

/-!
# Normalized truncation cut pairs

For a cochain-complex t-structure decomposition at cut `cut`, the lower
truncation lies strictly below the upper boundary.  This file names the
corresponding lower cut `cut - 1` so the decomposition lane uses
`truncLE(cut - 1, K) ⟶ K ⟶ truncGE(cut, K)`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The lower cut paired with an upper truncation boundary `cut`. -/
def decompositionLowerCut
    (cut : ℤ) :
    ℤ :=
  cut - 1

/-- Projection formula for the normalized lower cut. -/
theorem decompositionLowerCut_eq
    (cut : ℤ) :
    TraceAnalyticMotivicTStructure.decompositionLowerCut cut =
      cut - 1 :=
  rfl

/-- The lower truncation object paired with upper cut `cut`. -/
def additiveDecompositionTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticAdditiveCochainComplex :=
  TraceAnalyticMotivicTStructure.additiveTruncLE
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
    complex

/-- The lower inclusion map paired with upper cut `cut`. -/
def additiveDecompositionTruncLEInclusionMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex ⟶
      complex :=
  TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
    complex

/-- Projection formula for the paired lower truncation object. -/
theorem additiveDecompositionTruncLE_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex) :
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex =
      TraceAnalyticMotivicTStructure.additiveTruncLE (cut - 1) complex :=
  rfl

/-- Projection formula for the paired lower inclusion map. -/
theorem additiveDecompositionTruncLEInclusionMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap
        (cut - 1)
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
