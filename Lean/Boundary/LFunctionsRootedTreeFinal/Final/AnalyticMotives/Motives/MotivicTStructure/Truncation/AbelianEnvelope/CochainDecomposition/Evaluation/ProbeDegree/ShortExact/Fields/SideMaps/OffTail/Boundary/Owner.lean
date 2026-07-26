import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.OffTail.Boundary.Cokernel.Owner

/-!
# Off-tail boundary upper-map epicity

This file owns epicity of the intrinsic upper map at the normalized boundary
degree `cut`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- At the upper boundary degree, the intrinsic second evaluated map is epic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_boundary_epi_g_of_exact_epi
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
          cut).Exact)
    (hepi :
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            cut).g) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          cut).g :=
  epi_of_isColimit_cofork
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_boundary_g_isCokernel_f_of_exact_epi
        cut
        complex
        probe
        hnone
        hexact
        hepi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
