import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.ShortExact.Fields.SideMaps.LowerTail.Boundary.Kernel.Owner

/-!
# Lower-tail boundary monicity

This file owns the boundary case of monicity for the first map in the
intrinsic evaluated abelian-envelope truncation short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- At the normalized lower boundary degree, the intrinsic first evaluated map
is monic whenever the boundary short complex is exact and the first map is
monic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_zero_mono_f_of_exact_mono
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hexact :
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (0 : ℤ))).Exact)
    (hmono :
      Mono
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (0 : ℤ))).f) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (0 : ℤ))).f :=
  mono_of_isLimit_fork
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_zero_f_isKernel_g_of_exact_mono
        cut
        complex
        probe
        hexact
        hmono)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
