import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Away.Owner

/-!
# Off-tail boundary exactness

This file owns exactness of the intrinsic evaluated short complex at the
upper boundary degree `cut`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- At the upper boundary degree, the intrinsic evaluated truncation short
complex is exact when supplied by the boundary handoff. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_boundary_exact_of_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r cut =
        none)
    (hexact :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          cut).Exact) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        cut).Exact :=
  hexact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
