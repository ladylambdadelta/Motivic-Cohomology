import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Exactness.LowerTail.Boundary.Owner

/-!
# Positive lower-tail exactness

This file owns the successor-tail, nonboundary exactness case for the
intrinsic evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- At positive normalized lower-tail degrees, the intrinsic evaluated
truncation short complex is exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_exact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (Nat.succ lowerTail : ℤ))).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_lowerTail_isIso_f
      cut
      complex
      probe
      (Nat.succ lowerTail)
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_isIso_f
          cut
          complex
          probe
          lowerTail)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
