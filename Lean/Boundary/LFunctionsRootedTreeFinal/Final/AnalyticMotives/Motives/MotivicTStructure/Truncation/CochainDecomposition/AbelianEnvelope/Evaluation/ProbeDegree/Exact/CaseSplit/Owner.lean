import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.LowerTail.Surjective.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.OffLowerTail.Injective.Owner

/-!
# Probe-degree exactness by lower-tail case split

This file assembles the two concrete support cases for the normalized
truncation decomposition.  A degree either lies in the paired lower-tail
embedding, where exactness is supplied by lower-tail surjectivity, or it lies
outside that embedding, where exactness is supplied by off-tail injectivity.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree exactness follows by splitting a degree according to the
paired lower-tail embedding. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_lowerTail_or_offLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlower :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).Exact)
    (hoff :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).Exact)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  match htail :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
          degree with
  | none =>
      hoff degree htail
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
          hlower lowerTail

/-- Surjectivity on every lower-tail component and injectivity off the lower
tail prove probe-degree exactness in every degree. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeExact_of_lowerTail_surjective_offLowerTail_injective
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlower :
      ∀ lowerTail : ℕ,
        Function.Surjective
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).f)
    (hoff :
      ∀ degree : ℤ,
        (TraceAnalyticMotivicTStructure.truncLEEmbedding
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
          none →
        Function.Injective
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
      degree).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeExact_of_lowerTail_or_offLowerTail
    cut
    complex
    probe
    (fun lowerTail =>
      TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_surjective_f
        cut
        complex
        probe
        lowerTail
        (hlower lowerTail))
    (fun degree hnone =>
      TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_injective_g
        cut
        complex
        probe
        degree
        hnone
        (hoff degree hnone))
    degree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
