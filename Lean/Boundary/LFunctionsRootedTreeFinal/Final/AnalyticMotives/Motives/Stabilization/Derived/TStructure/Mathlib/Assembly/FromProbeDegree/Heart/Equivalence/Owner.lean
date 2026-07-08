import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.FromProbeDegree.Heart.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Mathlib.Assembly.Heart.GlobalShortExact.Equivalence.Owner

/-!
# Heart equivalence from global probe-degree data

This file specializes the homological/categorical heart equivalence to the
Mathlib t-structure assembled from global analytic probe-degree exactness.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The existing homological heart is equivalent to the categorical heart of
the global-orthogonality/global-probe-degree t-structure. -/
def HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalProbeDegree
            zeroField
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalShortExact
    zeroField
    (TraceAnalyticDerivedMotiveCategory.globalCochainPreimageShortExact_of_globalProbeDegree_casewise
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi)
    cut

/-- The functor of the global-probe-degree heart equivalence is the
homological-to-categorical heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree_functor
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).functor =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut :=
  rfl

/-- The inverse of the global-probe-degree heart equivalence is the
categorical-to-homological heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree_inverse
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).inverse =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut :=
  rfl

/-- The functor of the orthogonality/global-probe heart equivalence preserves
the ambient derived-motive inclusion. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree_functor_comp_inclusion
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).functor ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalProbeDegree
            zeroField
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut :=
  rfl

/-- The inverse of the orthogonality/global-probe heart equivalence preserves
the ambient derived-motive inclusion. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree_inverse_comp_inclusion
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfOrthogonalityAndGlobalProbeDegree
        zeroField
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).inverse ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfOrthogonalityAndGlobalProbeDegree
            zeroField
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut :=
  rfl

/-- The existing homological heart is equivalent to the categorical heart of
the global-postcomposition/global-probe-degree t-structure. -/
def HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
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
    (cut : ℤ) :
    TraceAnalyticDerivedMotiveCategory.HomologicalHeart cut ≌
      TraceAnalyticDerivedMotiveCategory.TStructureHeart
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
            postcompVanishing
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut :=
  TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalShortExact
    postcompVanishing
    (TraceAnalyticDerivedMotiveCategory.globalCochainPreimageShortExact_of_globalProbeDegree_casewise
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi)
    cut

/-- The functor of the global-probe-degree postcomposition heart equivalence
is the homological-to-categorical heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_functor
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).functor =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.toTStructureHeartFunctorOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut :=
  rfl

/-- The inverse of the global-probe-degree postcomposition heart equivalence
is the categorical-to-homological heart transport functor. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_inverse
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).inverse =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.toHomologicalHeartFunctorOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut :=
  rfl

/-- The functor of the postcomposition/global-probe heart equivalence
preserves the ambient derived-motive inclusion. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_functor_comp_inclusion
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).functor ⋙
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
            postcompVanishing
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut =
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut :=
  rfl

/-- The inverse of the postcomposition/global-probe heart equivalence
preserves the ambient derived-motive inclusion. -/
theorem HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree_inverse_comp_inclusion
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
    (cut : ℤ) :
    (TraceAnalyticDerivedMotiveCategory.HomologicalHeart.equivalenceTStructureHeartOfGlobalPostcompVanishingAndGlobalProbeDegree
        postcompVanishing
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
        cut).inverse ⋙
      TraceAnalyticDerivedMotiveCategory.HomologicalHeart.inclusion cut =
      TraceAnalyticDerivedMotiveCategory.TStructureHeart.inclusion
        (TraceAnalyticDerivedMotiveCategory
          .tStructureOfGlobalPostcompVanishingAndGlobalProbeDegree
            postcompVanishing
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)
        cut :=
  rfl

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
