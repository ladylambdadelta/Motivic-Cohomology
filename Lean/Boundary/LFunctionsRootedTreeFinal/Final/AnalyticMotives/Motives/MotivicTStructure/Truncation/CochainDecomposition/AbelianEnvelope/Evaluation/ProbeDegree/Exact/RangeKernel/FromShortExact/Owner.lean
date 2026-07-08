import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.RangeKernel.FromCochain.Owner

/-!
# Range-kernel equality from cochain short exactness

This file records the forward concrete range-kernel consequence of
cochain-level short exactness of the Yoneda truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Cochain-level short exactness of the Yoneda abelian-envelope truncation
decomposition implies the range-kernel equality for every named probe-degree
Q-module truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_range_eq_ker_of_cochainShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
          cut
          complex)) :
    LinearMap.range
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f =
      LinearMap.ker
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  abelianEnvelopeCochainDecompositionProbeDegree_range_eq_ker_of_cochainExact
    cut
    complex
    probe
    degree
    (TraceAnalyticAbelianCochainComplex.shortExact_exact hshortExact)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
