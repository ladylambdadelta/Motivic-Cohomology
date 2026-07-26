import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Exactness.OffTail.Away.Owner

/-!
# Off-tail intrinsic probe-degree exactness

This file owns exactness off the paired lower-tail embedding for the intrinsic
evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Off the paired lower-tail embedding, the intrinsic evaluated truncation
short complex is exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_exact_owner
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
  match
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecomposition_offTail_eq_or_cut_lt
          cut
          degree
          hnone with
  | Or.inl hboundary =>
    Eq.ndrec
      (motive := fun boundaryDegree =>
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            boundaryDegree).Exact)
      boundaryExact
      hboundary.symm
  | Or.inr hdegree =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_exact
        cut
        complex
        probe
        degree
        hnone
        hdegree

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
