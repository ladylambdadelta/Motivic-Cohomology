import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.Owner

/-!
# Current cochain-preimage exactness from probe-degree analysis

This file keeps the current truncation-field constructor tied to its analytic
source theorem: short exactness of the intrinsic abelian-envelope decomposition
of the canonical cochain preimage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Probe-degree lower-tail and off-tail analytic data prove short exactness
of the intrinsic normalized decomposition of the canonical cochain preimage. -/
theorem current_cochainPreimage_shortExact_of_probeDegree_casewise
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
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
                degree).g) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_probeDegree_casewise
      1
      (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- Degreewise short exactness proves short exactness of the intrinsic
normalized decomposition of the canonical cochain preimage. -/
theorem current_cochainPreimage_shortExact_of_degreewiseShortExact
    (object : TraceAnalyticDerivedMotiveCategory)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise
      1
      (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
      hdegree

/-- The current Mathlib-shape truncation-existence field is obtained by first
proving the canonical cochain-preimage short exactness theorem. -/
theorem current_exists_triangle_zero_one_field_of_probeDegree_shortExact
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
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
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .current_exists_triangle_zero_one_field_of_shortExact
      object
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_shortExact_of_probeDegree_casewise
          object
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Degreewise short exactness of the canonical cochain-preimage
decomposition gives the current Mathlib-shape truncation-existence field. -/
theorem current_exists_triangle_zero_one_field_of_degreewiseShortExact
    (object : TraceAnalyticDerivedMotiveCategory)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  TraceAnalyticDerivedMotiveCategory
    .current_exists_triangle_zero_one_field_of_shortExact
      object
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_shortExact_of_degreewiseShortExact
          object
          hdegree)

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
