import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Away.Owner

/-!
# Off-tail intrinsic probe-degree upper map epicity

This file owns the nonzero off-lower-tail side map in the intrinsic evaluated
abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Off the paired lower-tail embedding, the intrinsic second evaluated map is
epic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_epi_g_owner
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (boundaryEpi :
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            cut).g)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  match
      TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecomposition_offTail_eq_or_cut_lt
          cut
          degree
          hnone with
  | Or.inl hboundary =>
    Eq.ndrec
      (motive := fun boundaryDegree =>
        Epi
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              boundaryDegree).g)
      boundaryEpi
      hboundary.symm
  | Or.inr hdegree =>
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_away_epi_g
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
