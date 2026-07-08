import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Exact.CaseSplit.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Support.EpiMono.Owner

/-!
# Intrinsic probe-degree short exactness by lower-tail case split

This file upgrades the intrinsic lower-tail exactness case split to short
exactness using explicit mono and epi side fields.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic probe-degree short exactness follows by splitting a degree
according to the paired lower-tail embedding. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_lowerTail_or_offLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlowerExact :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ lowerTail : ℕ,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
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
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).ShortExact :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      { exact := hoffExact degree htail
        mono_f :=
          TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_mono_f_of_lowerTail_none
              cut
              complex
              probe
              degree
              htail
        epi_g := hoffEpi degree htail }
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
          { exact := hlowerExact lowerTail
            mono_f := hlowerMono lowerTail
            epi_g :=
              TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex_epi_g_of_lowerTail
                  cut
                  complex
                  probe
                  lowerTail }

/-- Lower-tail exactness and monicity, together with off-lower-tail exactness
and epicity, give intrinsic short exactness in every evaluated probe degree. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_casewise_exact_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlowerExact :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ lowerTail : ℕ,
        Mono
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
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
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).ShortExact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_lowerTail_or_offLowerTail
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
