import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.Owner

/-!
# Probe-degree short exactness by lower-tail case split

This file upgrades the concrete lower-tail exactness case split to short
exactness.  The zero object on the vanished side supplies one mono/epi field;
the remaining nonzero map is kept as an explicit input.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree short exactness follows by splitting a degree according to the
paired lower-tail embedding. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_lowerTail_or_offLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlowerExact :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ lowerTail : ℕ,
        Mono
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
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
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailShortExact_of_exact_epi_g
          cut
          complex
          probe
          degree
          htail
          (hoffExact degree htail)
          (hoffEpi degree htail)
  | some lowerTail =>
      let hdegree :
          TraceAnalyticMotivicTStructure.decompositionLowerCut cut -
              (lowerTail : ℤ) =
            degree :=
        ComplexShape.Embedding.f_eq_of_r_eq_some
          (e :=
            TraceAnalyticMotivicTStructure.truncLEEmbedding
              (TraceAnalyticMotivicTStructure.decompositionLowerCut cut))
          htail
      match hdegree with
      | rfl =>
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeLowerTailShortExact_of_exact_mono_f
              cut
              complex
              probe
              lowerTail
              (hlowerExact lowerTail)
              (hlowerMono lowerTail)

/-- Lower-tail exactness and monicity, together with off-lower-tail exactness
and epicity, give short exactness in every evaluated probe degree. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_casewise_exact_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlowerExact :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ lowerTail : ℕ,
        Mono
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
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
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_lowerTail_or_offLowerTail
      cut
      complex
      probe
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      degree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
