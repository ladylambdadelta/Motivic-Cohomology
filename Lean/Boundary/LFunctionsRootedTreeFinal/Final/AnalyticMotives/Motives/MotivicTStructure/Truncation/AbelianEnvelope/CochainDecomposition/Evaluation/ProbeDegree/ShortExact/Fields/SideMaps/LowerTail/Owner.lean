import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Successor.Owner

/-!
# Lower-tail intrinsic probe-degree lower map monicity

This file owns the nonzero lower-tail side map in the intrinsic evaluated
abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On lower-tail degrees, the intrinsic first evaluated map is monic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_mono_f_owner
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (boundaryMono :
      Mono
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (0 : ℤ))).f)
    (lowerTail : ℕ) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f :=
  match lowerTail with
  | 0 =>
      boundaryMono
  | Nat.succ lowerTail =>
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_mono_f
          cut
          complex
          probe
          lowerTail

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
