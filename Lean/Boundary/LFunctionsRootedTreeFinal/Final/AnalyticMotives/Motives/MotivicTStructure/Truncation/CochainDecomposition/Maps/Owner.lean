import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CutPair.Owner

/-!
# Cochain-level normalized truncation decomposition maps

This file owns the two cochain-level maps in the normalized truncation
decomposition `truncLE(cut - 1, K) ⟶ K ⟶ truncGE(cut, K)` and their composite.
The composite-zero and exactness proofs live downstream of these concrete maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The cochain-level lower map in the normalized truncation decomposition. -/
def additiveCochainDecompositionLowerMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex ⟶
      complex :=
  TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
    cut
    complex

/-- The cochain-level upper map in the normalized truncation decomposition. -/
def additiveCochainDecompositionUpperMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    complex ⟶ TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
  TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap cut complex

/-- The cochain-level composite whose vanishing is the first exactness field
for the normalized truncation decomposition. -/
def additiveCochainDecompositionCompositeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE cut complex ⟶
      TraceAnalyticMotivicTStructure.additiveTruncGE cut complex :=
  TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
      cut
      complex ≫
    TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
      cut
      complex

/-- Projection formula for the cochain-level lower decomposition map. -/
theorem additiveCochainDecompositionLowerMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
        cut
        complex :=
  rfl

/-- Projection formula for the cochain-level upper decomposition map. -/
theorem additiveCochainDecompositionUpperMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
        cut
        complex :=
  rfl

/-- Projection formula for the cochain-level decomposition composite. -/
theorem additiveCochainDecompositionCompositeMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveCochainDecompositionCompositeMap
        cut
        complex =
      TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex ≫
        TraceAnalyticMotivicTStructure.additiveTruncGEProjectionMap
          cut
          complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
