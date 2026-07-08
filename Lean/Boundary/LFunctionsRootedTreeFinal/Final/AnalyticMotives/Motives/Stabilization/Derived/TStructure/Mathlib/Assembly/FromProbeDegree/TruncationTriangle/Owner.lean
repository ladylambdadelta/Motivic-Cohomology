import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Owner

/-!
# Truncation triangles from global-probe-degree assembled t-structures

This file exposes the adjacent truncation triangle supplied by the Mathlib
`TStructure`s assembled from global probe-degree exactness.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The t-structure assembled from global orthogonality and global
probe-degree data supplies an adjacent truncation triangle for every derived
analytic motive. -/
theorem existsTriangleZeroOne_tStructureOfOrthogonalityAndGlobalProbeDegree
    (zeroField :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              morphism = 0)
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            Mono
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                    (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).Exact)
    (hoffEpi :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            Epi
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  degree).g)
    (object : TraceAnalyticDerivedMotiveCategory) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  (TraceAnalyticDerivedMotiveCategory
    .tStructureOfOrthogonalityAndGlobalProbeDegree
      zeroField
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi).exists_triangle_zero_one object

/-- The t-structure assembled from global postcomposition vanishing and
global probe-degree data supplies an adjacent truncation triangle for every
derived analytic motive. -/
theorem existsTriangleZeroOne_tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
    (postcompVanishing :
      ∀ {source target : TraceAnalyticDerivedMotiveCategory},
        ∀ (morphism : source ⟶ target),
          TraceAnalyticDerivedMotiveCategory.tStructureLE 0 source →
            TraceAnalyticDerivedMotiveCategory.tStructureGE 1 target →
              ∀ (probe : TraceAnalyticDerivedMotiveCategoryᵒᵖ),
                ∀ hom : probe.unop ⟶ source,
                  hom ≫ morphism = 0)
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ lowerTail : ℕ,
            Mono
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                    (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).Exact)
    (hoffEpi :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          ∀ degree : ℤ,
            (TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
                degree =
              none →
            Epi
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                  1
                  (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                  probe
                  degree).g)
    (object : TraceAnalyticDerivedMotiveCategory) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.tStructureGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  (TraceAnalyticDerivedMotiveCategory
    .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
      postcompVanishing
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi).exists_triangle_zero_one object

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
