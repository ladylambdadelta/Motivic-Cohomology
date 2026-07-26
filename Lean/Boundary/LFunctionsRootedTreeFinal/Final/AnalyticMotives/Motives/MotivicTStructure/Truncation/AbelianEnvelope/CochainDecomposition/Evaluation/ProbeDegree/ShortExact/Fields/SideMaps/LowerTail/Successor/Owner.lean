import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Boundary.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Successor.IsIso.Owner

/-!
# Positive lower-tail monicity

This file owns the successor-tail, nonboundary case of monicity for the first
map in the intrinsic evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- At positive normalized lower-tail degrees, the intrinsic first evaluated
map is monic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_succ_mono_f
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (Nat.succ lowerTail : ℤ))).f :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_mono_f_of_lowerTail_isIso_f
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
