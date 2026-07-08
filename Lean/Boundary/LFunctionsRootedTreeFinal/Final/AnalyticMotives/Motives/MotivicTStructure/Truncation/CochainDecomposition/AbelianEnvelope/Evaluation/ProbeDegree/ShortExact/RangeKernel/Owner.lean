import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.Owner

/-!
# Probe-degree short exactness from range-kernel data

This file packages the concrete linear-algebra endpoint for evaluated
truncation short complexes: range-kernel equality, injectivity of the lower
map, and surjectivity of the upper map imply short exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Range-kernel equality plus ordinary injectivity and surjectivity of the two
named Q-module maps gives short exactness of the named probe-degree truncation
short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_range_eq_ker_injective_surjective
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hrange :
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
            degree).g)
    (hinjective :
      Function.Injective
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f)
    (hsurjective :
      Function.Surjective
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g) :
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_injective_surjective
    cut
    complex
    probe
    degree
    (abelianEnvelopeCochainDecompositionProbeDegreeExact_of_range_eq_ker
      cut
      complex
      probe
      degree
      hrange)
    hinjective
    hsurjective

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
