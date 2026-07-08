import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TruncationTriangle.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.FromProbeDegree.Owner

/-!
# Derived truncation triangle from probe-degree exactness

This file constructs the distinguished derived truncation triangle directly
from the concrete probe-degree lower-tail and off-tail exactness fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The cochain-level short exactness witness assembled from concrete
probe-degree lower-tail and off-tail exactness data. -/
def abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortComplex cut complex) :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
      cut
      complex
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

/-- The derived truncation triangle obtained directly from concrete
probe-degree lower-tail and off-tail exactness data. -/
def abelianEnvelopeCochainDecompositionDerivedTriangleOfProbeDegreeCasewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    Triangle TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- The probe-degree derived truncation triangle is distinguished. -/
theorem abelianEnvelopeCochainDecompositionDerivedTriangleOfProbeDegreeCasewise_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDerivedTriangleOfProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi ∈
      distTriang TraceAnalyticDerivedMotiveCategory :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDerivedTriangle_distinguished
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExactFromProbeDegreeCasewise
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
