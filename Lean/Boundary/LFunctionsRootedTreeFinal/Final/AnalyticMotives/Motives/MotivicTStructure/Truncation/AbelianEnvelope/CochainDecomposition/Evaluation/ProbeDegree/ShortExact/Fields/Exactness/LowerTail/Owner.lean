import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.Exactness.LowerTail.Successor.Owner

/-!
# Lower-tail intrinsic probe-degree exactness

This file owns exactness on normalized lower-tail degrees for the intrinsic
evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- On lower-tail degrees, the intrinsic evaluated truncation short complex is
exact. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_exact_owner
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
  match lowerTail with
  | 0 =>
      boundaryExact
  | Nat.succ lowerTail =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_exact
          cut
          complex
          probe
          lowerTail

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
