import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.ProbeDegree.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Owner

/-!
# Current cochain-preimage short exactness from trace calculus

This file owns the canonical short-exactness theorem for the intrinsic
truncation decomposition of every derived analytic motive's cochain preimage.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- Trace calculus proves lower-tail monicity of the intrinsic first evaluated
map for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_lowerTail_mono_f_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (0 : ℤ))).f) :
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
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_mono_f
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        probe
        (boundaryMono probe)
        lowerTail

/-- Trace calculus proves off-lower-tail epicity of the intrinsic second
evaluated map for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_offTail_epi_g_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              1).g) :
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
  fun probe degree hnone =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_epi_g
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        probe
        (boundaryEpi probe)
        degree
        hnone

/-- Trace calculus proves lower-tail exactness of the intrinsic probe-degree
decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_lowerTail_exact_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (0 : ℤ))).Exact) :
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
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_exact
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        probe
        (boundaryExact probe)
        lowerTail

/-- Trace calculus proves lower-tail monicity of the intrinsic probe-degree
decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_lowerTail_mono_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (0 : ℤ))).f) :
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
    TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_lowerTail_mono_f_field_of_traceCalculus
      object
      boundaryMono
      probe
      lowerTail

/-- Trace calculus proves off-tail exactness of the intrinsic probe-degree
decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_offTail_exact_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            1).Exact) :
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
  fun probe degree hnone =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_exact
        1
        (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
        probe
        (boundaryExact probe)
        degree
        hnone

/-- Trace calculus proves off-tail epicity of the intrinsic probe-degree
decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_offTail_epi_field_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              1).g) :
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
  fun probe degree hnone =>
    TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_offTail_epi_g_field_of_traceCalculus
      object
      boundaryEpi
      probe
      degree
      hnone

/-- Trace calculus supplies short exactness of the intrinsic truncation
decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_shortExact_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (lowerBoundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (0 : ℤ))).Exact)
    (lowerBoundaryMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (0 : ℤ))).f)
    (upperBoundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            1).Exact)
    (upperBoundaryEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              1).g) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          1
          (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_shortExact_of_probeDegree_casewise
      object
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_probeDegree_lowerTail_exact_field_of_traceCalculus
          object
          lowerBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_probeDegree_lowerTail_mono_field_of_traceCalculus
          object
          lowerBoundaryMono)
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_probeDegree_offTail_exact_field_of_traceCalculus
          object
          upperBoundaryExact)
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_probeDegree_offTail_epi_field_of_traceCalculus
          object
          upperBoundaryEpi)

/-- Trace calculus supplies degreewise short exactness of the intrinsic
truncation decomposition for every canonical cochain preimage. -/
theorem current_cochainPreimage_degreewiseShortExact_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (lowerBoundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (0 : ℤ))).Exact)
    (lowerBoundaryMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (0 : ℤ))).f)
    (upperBoundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            1).Exact)
    (upperBoundaryEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              1).g) :
    ∀ degree : ℤ,
      ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)).map
        (HomologicalComplex.eval
          TraceAnalyticAdditiveAbelianEnvelope
          (ComplexShape.up ℤ)
          degree)).ShortExact :=
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_degreewiseShortExact_of_shortExact
      object
      (TraceAnalyticDerivedMotiveCategory
        .current_cochainPreimage_shortExact_of_traceCalculus
          object
          lowerBoundaryExact
          lowerBoundaryMono
          upperBoundaryExact
          upperBoundaryEpi)

/-- Trace calculus supplies lower-tail intrinsic probe-degree exactness for
every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_lowerTail_exact_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (0 : ℤ))).Exact) :
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
              (lowerTail : ℤ))).Exact :=
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_lowerTail_exact_field_of_traceCalculus
      object
      boundaryExact

/-- Trace calculus supplies lower-tail intrinsic probe-degree monicity for
every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_lowerTail_mono_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (0 : ℤ))).f) :
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
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_lowerTail_mono_field_of_traceCalculus
      object
      boundaryMono

/-- Trace calculus supplies off-tail intrinsic probe-degree exactness for
every canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_offTail_exact_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
            probe
            1).Exact) :
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
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_offTail_exact_field_of_traceCalculus
      object
      boundaryExact

/-- Trace calculus supplies off-tail intrinsic probe-degree epicity for every
canonical cochain preimage. -/
theorem current_cochainPreimage_probeDegree_offTail_epi_of_traceCalculus
    (object : TraceAnalyticDerivedMotiveCategory)
    (boundaryEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              1).g) :
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
  TraceAnalyticDerivedMotiveCategory
    .current_cochainPreimage_probeDegree_offTail_epi_field_of_traceCalculus
      object
      boundaryEpi

end TraceAnalyticDerivedMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
