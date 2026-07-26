import Mathlib.Algebra.Homology.ShortComplex.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Support.EpiMono.Owner

/-!
# Off-tail boundary cokernel property

This file owns the boundary universal property for the second map in the
intrinsic evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- At the upper boundary degree, the intrinsic second evaluated map is a
cokernel of the intrinsic first evaluated map whenever the boundary short
complex is exact and the second map is epic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_offTail_boundary_g_isCokernel_f_of_exact_epi
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
    IsColimit
      (CokernelCofork.ofπ
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            cut).g
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            cut).zero) := by
  let S :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        cut
  letI : Epi S.g := hepi
  exact hexact.gIsCokernel

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
