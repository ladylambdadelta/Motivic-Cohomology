import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Exact.Owner

/-!
# Intrinsic probe-degree exactness by lower-tail case split

This file assembles lower-tail and off-lower-tail exactness inputs for the
intrinsic abelian-envelope truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Intrinsic probe-degree exactness follows by splitting a degree according to
the paired lower-tail embedding. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeExact_of_lowerTail_or_offLowerTail
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hlower :
      ∀ lowerTail : ℕ,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hoff :
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
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
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

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
