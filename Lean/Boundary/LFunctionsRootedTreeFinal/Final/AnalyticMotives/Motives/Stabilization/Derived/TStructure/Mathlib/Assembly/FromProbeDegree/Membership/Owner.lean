import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Projections.Owner

/-!
# Membership bridges for probe-degree assembled Mathlib t-structures

This file gives the Mathlib `IsLE` and `IsGE` membership bridges for the
t-structures assembled from global probe-degree analytic data.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Analytic `≤` membership gives Mathlib `IsLE` membership for the
orthogonality/global-probe-degree assembled t-structure. -/
theorem isLE_tStructureOfOrthogonalityAndGlobalProbeDegree_of_tStructureLE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsLE object degree where
  le := membership

/-- Analytic `≥` membership gives Mathlib `IsGE` membership for the
orthogonality/global-probe-degree assembled t-structure. -/
theorem isGE_tStructureOfOrthogonalityAndGlobalProbeDegree_of_tStructureGE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsGE object degree where
  ge := membership

/-- Analytic `≤` membership gives Mathlib `IsLE` membership for the
postcomposition/global-probe-degree assembled t-structure. -/
theorem isLE_tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_of_tStructureLE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureLE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsLE object degree where
  le := membership

/-- Analytic `≥` membership gives Mathlib `IsGE` membership for the
postcomposition/global-probe-degree assembled t-structure. -/
theorem isGE_tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree_of_tStructureGE
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      TraceAnalyticDerivedMotiveCategory.tStructureGE degree object) :
    (TraceAnalyticDerivedMotiveCategory
      .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi).IsGE object degree where
  ge := membership

/-- Mathlib `IsLE` membership for the orthogonality/global-probe-degree
assembled t-structure gives analytic `≤` membership. -/
theorem tStructureLE_of_isLE_tStructureOfOrthogonalityAndGlobalProbeDegree
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndGlobalProbeDegree
          zeroField
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi).IsLE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE degree object :=
  membership.le

/-- Mathlib `IsGE` membership for the orthogonality/global-probe-degree
assembled t-structure gives analytic `≥` membership. -/
theorem tStructureGE_of_isGE_tStructureOfOrthogonalityAndGlobalProbeDegree
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfOrthogonalityAndGlobalProbeDegree
          zeroField
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi).IsGE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE degree object :=
  membership.ge

/-- Mathlib `IsLE` membership for the postcomposition/global-probe-degree
assembled t-structure gives analytic `≤` membership. -/
theorem tStructureLE_of_isLE_tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi).IsLE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE degree object :=
  membership.le

/-- Mathlib `IsGE` membership for the postcomposition/global-probe-degree
assembled t-structure gives analytic `≥` membership. -/
theorem tStructureGE_of_isGE_tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (degree : ℤ)
    (membership :
      (TraceAnalyticDerivedMotiveCategory
        .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
          postcompVanishing
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi).IsGE object degree) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE degree object :=
  membership.ge

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
