import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.FromProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.Constructors.CochainShortExact.Owner

/-!
# Probe-degree constructors for Yoneda truncation representatives

This file promotes the concrete probe-degree casewise analytic truncation
calculus to the public `HasYonedaTruncationRepresentative` predicate for the
represented derived object.
-/

noncomputable section

open CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree casewise exactness plus the lower-tail mono and off-tail epi
fields give the public Yoneda truncation representative predicate for the
represented derived object. -/
theorem hasYonedaTruncationRepresentativeOfProbeDegreeCasewise
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
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      cut
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfCochainShortExact
      cut
      complex
      hasHomology
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          complex
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Normalized cut-`1` constructor from probe-degree casewise analytic data. -/
theorem hasYonedaTruncationRepresentativeOneOfProbeDegreeCasewise
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              (1 - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                (1 - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                degree).g) :
    TraceAnalyticMotivicTStructure.HasYonedaTruncationRepresentative
      1
      (TraceAnalyticDerivedMotiveCategory.objectOf
        (TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex complex)) :=
  TraceAnalyticMotivicTStructure
    .hasYonedaTruncationRepresentativeOfProbeDegreeCasewise
      1
      complex
      hasHomology
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
