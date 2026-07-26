import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Owner

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

/-- Short exactness of the canonical cochain preimage recovers its degreewise
short-exact field. -/
theorem current_cochainPreimage_degreewiseShortExact_of_shortExact
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∀ degree : ℤ,
      ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).ShortExact :=
  (TraceAnalyticAbelianCochainComplex.shortExact_iff_degreewise_shortExact
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))).mp
    hshortExact

/-- Degreewise short exactness of the canonical cochain preimage gives the
lower-tail intrinsic probe-degree exactness field. -/
theorem current_cochainPreimage_probeDegree_lowerTail_exact_of_degreewiseShortExact
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
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (lowerTail : ℤ))).Exact :=
  fun probe lowerTail =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_degreewiseShortExact
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        hdegree
        probe
        (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
          (lowerTail : ℤ))

/-- Degreewise short exactness of the canonical cochain preimage gives the
lower-tail intrinsic probe-degree monicity field. -/
theorem current_cochainPreimage_probeDegree_lowerTail_mono_of_degreewiseShortExact
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
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      ∀ lowerTail : ℕ,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).f :=
  fun probe lowerTail =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_mono_f_of_degreewiseShortExact
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        hdegree
        probe
        (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
          (lowerTail : ℤ))

/-- Degreewise short exactness of the canonical cochain preimage gives the
off-tail intrinsic probe-degree exactness field. -/
theorem current_cochainPreimage_probeDegree_offTail_exact_of_degreewiseShortExact
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
            degree).Exact :=
  fun probe degree degreeMembership =>
    (fun degreeMembershipConfirmed =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_degreewiseShortExact
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hdegree
          probe
          degree)
      degreeMembership

/-- Degreewise short exactness of the canonical cochain preimage gives the
off-tail intrinsic probe-degree epicity field. -/
theorem current_cochainPreimage_probeDegree_offTail_epi_of_degreewiseShortExact
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
              degree).g :=
  fun probe degree degreeMembership =>
    (fun degreeMembershipConfirmed =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_epi_g_of_degreewiseShortExact
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
          hdegree
          probe
          degree)
      degreeMembership

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
