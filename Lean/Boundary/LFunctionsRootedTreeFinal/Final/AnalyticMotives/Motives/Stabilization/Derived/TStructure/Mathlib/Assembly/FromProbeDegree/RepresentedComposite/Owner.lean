import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Membership.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Orthogonality.RepresentedComposite.Owner

/-!
# Represented composites in the global-probe-degree assembled t-structure

This file transports the represented truncation composite data into the
Mathlib `TStructure` assembled from global probe-degree exactness.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The chosen lower vertex of a represented truncation object is `≤ 0` for
the Mathlib t-structure assembled from global probe-degree data. -/
theorem lowerObject_isLE_tStructureOfOrthogonalityAndGlobalProbeDegree
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
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsLE object.representative.lowerObject 0 :=
  TraceAnalyticDerivedMotiveCategory
    .isLE_tStructureOfOrthogonalityAndGlobalProbeDegree_of_tStructureLE
      zeroField
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object.representative.lowerObject
      0
      object.firstMap_source_mem_zero

/-- The chosen upper vertex of a represented truncation object is `≥ 1` for
the Mathlib t-structure assembled from global probe-degree data. -/
theorem upperObject_isGE_tStructureOfOrthogonalityAndGlobalProbeDegree
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
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsGE object.representative.upperObject 1 :=
  TraceAnalyticDerivedMotiveCategory
    .isGE_tStructureOfOrthogonalityAndGlobalProbeDegree_of_tStructureGE
      zeroField
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object.representative.upperObject
      1
      object.secondMap_target_mem_one

/-- The represented truncation composite is zero through the `zero'` field of
the Mathlib t-structure assembled from global probe-degree data. -/
theorem firstMap_secondMap_eq_zero_tStructureOfOrthogonalityAndGlobalProbeDegree
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
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.firstMap ≫ object.secondMap = 0 :=
  (TraceAnalyticDerivedMotiveCategory
    .tStructureOfOrthogonalityAndGlobalProbeDegree
      zeroField
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi).zero'
        (object.firstMap ≫ object.secondMap)
        object.firstMap_source_mem_zero
        object.secondMap_target_mem_one

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
