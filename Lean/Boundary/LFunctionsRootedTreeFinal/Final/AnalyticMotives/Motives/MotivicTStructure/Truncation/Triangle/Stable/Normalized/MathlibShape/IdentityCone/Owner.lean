import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.IdentityCone.Owner

/-!
# Identity-cone route to the Mathlib-shaped normalized triangle

This file records that the Mathlib-shaped normalized stable truncation triangle
comes equipped, under the cochain-level identity-cone hypothesis, with an
isomorphism from its associated short complex to the stable cochain
truncation-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- Under a cochain-level isomorphism of the normalized cone-to-upper map, the
Mathlib-shaped normalized stable truncation triangle exists and its associated
short complex is isomorphic to the stable cochain truncation-decomposition
short complex. -/
theorem stableNormalizedLowerInclusionTriangle_exists_with_cochainDecompositionComparison_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (∃ (lower upper : TraceAnalyticDMgmComparisonSource)
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
        TraceAnalyticDMgmComparisonSource.distinguishedTriangles) ∧
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_exists cut complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_isIso_cochainMap
        cut
        complex)

/-- The triangle component of the identity-cone Mathlib-shaped package is the
normalized stable lower-inclusion triangle. -/
theorem stableNormalizedLowerInclusionTriangle_identityConePackage_triangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_exists_with_cochainDecompositionComparison_isIso
        cut
        complex).left =
      TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionTriangle_exists cut complex :=
  rfl

/-- The short-complex component of the identity-cone Mathlib-shaped package is
the cochain-decomposition comparison isomorphism criterion. -/
theorem stableNormalizedLowerInclusionTriangle_identityConePackage_shortComplexComparison
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_exists_with_cochainDecompositionComparison_isIso
        cut
        complex).right =
      TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_isIso_cochainMap
          cut
          complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
