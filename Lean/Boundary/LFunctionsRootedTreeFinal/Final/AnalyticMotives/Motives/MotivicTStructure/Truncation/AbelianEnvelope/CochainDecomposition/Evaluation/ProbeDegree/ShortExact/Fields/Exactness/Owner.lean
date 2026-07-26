import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Exactness.OffTail.Owner

/-!
# Intrinsic probe-degree exactness fields

This file owns the boundary-sensitive exactness fields for the intrinsic
abelian-envelope normalized truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- On lower-tail degrees, the intrinsic evaluated truncation short complex is
exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (boundaryExact :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (0 : ℤ))).Exact)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_exact_owner
      cut
      complex
      probe
      boundaryExact
      lowerTail

/-- Off the paired lower-tail embedding, the intrinsic evaluated truncation
short complex is exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (boundaryExact :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          cut).Exact)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_exact_owner
      cut
      complex
      probe
      boundaryExact
      degree
      hnone

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
