import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Exactness.OffTail.Boundary.Owner

/-!
# Off-tail upper-away exactness

This file owns exactness of the intrinsic evaluated short complex away from
the upper boundary.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- In an off-lower-tail degree strictly above the upper boundary, the
intrinsic evaluated truncation short complex is exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut < degree) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_lowerTail_none_isIso_g
      cut
      complex
      probe
      degree
      hnone
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_isIso_g
          cut
          complex
          probe
          degree
          hnone
          hdegree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
