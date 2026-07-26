import Mathlib.Algebra.Homology.ShortComplex.Exact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Support.EpiMono.Owner

/-!
# Lower-tail boundary kernel property

This file owns the boundary universal property for the first map in the
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
is a kernel of the intrinsic second evaluated map whenever the boundary
short complex is exact and the first map is monic. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_lowerTail_zero_f_isKernel_g_of_exact_mono
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
    IsLimit
      (KernelFork.ofι
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (0 : ℤ))).f
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (0 : ℤ))).zero) := by
  let S :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (0 : ℤ))
  letI : Mono S.f := hmono
  exact hexact.fIsKernel

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
