import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Successor.Owner

/-!
# Lower-tail boundary exactness

This file owns the boundary case of exactness for the intrinsic evaluated
abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- At the normalized lower boundary degree, the intrinsic evaluated
truncation short complex is exact when supplied by the boundary handoff. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_zero_exact_of_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hexact :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (0 : ℤ))).Exact) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (0 : ℤ))).Exact :=
  hexact

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
