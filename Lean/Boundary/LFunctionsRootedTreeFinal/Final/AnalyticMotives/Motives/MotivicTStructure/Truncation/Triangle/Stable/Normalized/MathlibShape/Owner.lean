import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeVertex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.Projections.Owner

/-!
# Mathlib-shaped normalized stable truncation triangle

This file exposes the normalized stable truncation triangle in the existential
shape used by Mathlib's `TStructure.exists_triangle_zero_one` field.  The
aisle/coaisle membership proofs for its vertices are owned separately.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The normalized stable truncation triangle, displayed as an explicit
existential triangle with first vertex, third vertex, maps, and distinguished
membership. -/
theorem stableNormalizedLowerInclusionTriangle_exists
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ∃ (lower upper : TraceAnalyticDMgmComparisonSource)
      (firstMap :
        lower ⟶
          TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf complex))
      (secondMap :
        TraceAnalyticDMgmComparisonSource.objectOf
            (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
          upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  Exists.intro
    (TraceAnalyticDMgmComparisonSource.objectOf
      (TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)))
    (Exists.intro
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionConeVertex cut complex)
      (Exists.intro
        (TraceAnalyticDMgmComparisonSource.mapOf
          (TraceAnalyticAdditiveHomotopyCategory.mapOf
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
              cut
              complex)))
        (Exists.intro
          (TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionConeMap cut complex)
          (Exists.intro
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionConnectingMap cut complex)
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionTriangle_distinguished
                cut
                complex))))

/-- The first vertex in the Mathlib-shaped normalized stable truncation
triangle is the stable image of the paired lower truncation. -/
theorem stableNormalizedLowerInclusionTriangle_exists_firstVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Classical.choose
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionTriangle_exists cut complex) =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)) :=
  rfl

/-- The second vertex in the Mathlib-shaped normalized stable truncation
triangle is the normalized stable cone vertex. -/
theorem stableNormalizedLowerInclusionTriangle_exists_secondVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Classical.choose
        (Classical.choose_spec
          (TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionTriangle_exists cut complex)) =
      TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionConeVertex cut complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
