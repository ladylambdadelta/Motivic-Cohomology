import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.OffTailArithmetic.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Away.IsIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Boundary.Owner

/-!
# Off-tail upper-away upper-map epicity

This file owns epicity of the intrinsic upper map away from the upper
boundary.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- In an off-lower-tail degree strictly above the upper boundary, the
intrinsic second evaluated map is epic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_epi_g
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hdegree : cut < degree) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_epi_g_of_lowerTail_none_isIso_g
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
