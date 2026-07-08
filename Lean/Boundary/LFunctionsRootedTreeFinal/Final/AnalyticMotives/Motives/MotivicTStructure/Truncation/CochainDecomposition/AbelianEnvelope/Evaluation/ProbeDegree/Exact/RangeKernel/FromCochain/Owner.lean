import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.FromCochain.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.RangeKernel.Owner

/-!
# Range-kernel equality from cochain exactness

This file records the forward concrete consequence of cochain-level exactness:
after evaluating at a probe and degree, exactness is the equality between the
range of the lower map and the kernel of the upper map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Cochain-level exactness of the Yoneda abelian-envelope truncation
decomposition implies the range-kernel equality for every named probe-degree
Q-module truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_range_eq_ker_of_cochainExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      TraceAnalyticAbelianCochainComplex.exact
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
  (abelianEnvelopeCochainDecompositionProbeDegreeExact_iff_range_eq_ker
    cut
    complex
    probe
    degree).mp
    (abelianEnvelopeCochainDecompositionProbeDegreeExact_of_cochainExact
      cut
      complex
      probe
      degree
      hexact)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
