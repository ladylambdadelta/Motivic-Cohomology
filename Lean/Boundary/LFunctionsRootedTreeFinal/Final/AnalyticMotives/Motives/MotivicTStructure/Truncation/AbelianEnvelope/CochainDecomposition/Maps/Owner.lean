import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CutPair.Owner

/-!
# Abelian-envelope cochain truncation-decomposition maps

This file owns the maps in the abelian-envelope normalized truncation
decomposition
`truncLE(cut - 1,K) ⟶ K ⟶ truncGE(cut,K)`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The abelian-envelope lower object in the normalized truncation
decomposition. -/
def abelianEnvelopeDecompositionTruncLE
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticAbelianCochainComplex :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLE
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
    complex

/-- The abelian-envelope lower map in the normalized truncation
decomposition. -/
def abelianEnvelopeCochainDecompositionLowerMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeDecompositionTruncLE
        cut
        complex ⟶
      complex :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
    (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
    complex

/-- The abelian-envelope upper map in the normalized truncation
decomposition. -/
def abelianEnvelopeCochainDecompositionUpperMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    complex ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEProjectionMap
    cut
    complex

/-- The abelian-envelope composite whose vanishing is the first exactness field
for the normalized truncation decomposition. -/
def abelianEnvelopeCochainDecompositionCompositeMap
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure.abelianEnvelopeDecompositionTruncLE
        cut
        complex ⟶
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGE cut complex :=
  TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionLowerMap cut complex ≫
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionUpperMap cut complex

/-- Projection formula for the abelian-envelope lower decomposition map. -/
theorem abelianEnvelopeCochainDecompositionLowerMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionLowerMap cut complex =
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncLEInclusionMap
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
        complex :=
  rfl

/-- Projection formula for the abelian-envelope upper decomposition map. -/
theorem abelianEnvelopeCochainDecompositionUpperMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionUpperMap cut complex =
      TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEProjectionMap
        cut
        complex :=
  rfl

/-- Projection formula for the abelian-envelope decomposition composite. -/
theorem abelianEnvelopeCochainDecompositionCompositeMap_eq
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionCompositeMap cut complex =
      TraceAnalyticMotivicTStructure
          .abelianEnvelopeTruncLEInclusionMap
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            complex ≫
        TraceAnalyticMotivicTStructure.abelianEnvelopeTruncGEProjectionMap
          cut
          complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
