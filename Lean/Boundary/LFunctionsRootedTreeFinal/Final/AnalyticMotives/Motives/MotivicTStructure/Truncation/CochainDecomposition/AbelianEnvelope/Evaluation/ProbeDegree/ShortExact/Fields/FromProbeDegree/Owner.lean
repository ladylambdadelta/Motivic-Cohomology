import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.FromProbeDegree.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.Fields.FromCochain.Owner

/-!
# Probe-degree fields from casewise probe-degree truncation data

This file specializes the cochain-level short-exact field projections to the
casewise probe-degree exactness theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Casewise probe-degree data imply exactness of every named probe-degree
Q-module truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_exact_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionProbeDegree_exact_of_cochainShortExact
      cut
      complex
      probe
      degree
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          complex
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Casewise probe-degree data imply monicity of every named probe-degree
lower truncation map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_mono_f_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Mono
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionProbeDegree_mono_f_of_cochainShortExact
      cut
      complex
      probe
      degree
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          complex
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Casewise probe-degree data imply epicity of every named probe-degree upper
truncation map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_epi_g_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Epi
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionProbeDegree_epi_g_of_cochainShortExact
      cut
      complex
      probe
      degree
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
          cut
          complex
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
