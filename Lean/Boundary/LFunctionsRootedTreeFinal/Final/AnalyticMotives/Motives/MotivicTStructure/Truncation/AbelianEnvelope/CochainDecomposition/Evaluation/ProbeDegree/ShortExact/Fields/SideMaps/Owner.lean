import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Owner

/-!
# Intrinsic probe-degree side-map fields

This file owns the side-map fields for the two supported pieces of the
intrinsic abelian-envelope normalized truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- On lower-tail degrees, the intrinsic first evaluated map is monic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_mono_f
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
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_mono_f_owner
      cut
      complex
      probe
      boundaryMono
      lowerTail

/-- Off the paired lower-tail embedding, the intrinsic second evaluated map is
epic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_epi_g
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
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_epi_g_owner
      cut
      complex
      probe
      boundaryEpi
      degree
      hnone

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
