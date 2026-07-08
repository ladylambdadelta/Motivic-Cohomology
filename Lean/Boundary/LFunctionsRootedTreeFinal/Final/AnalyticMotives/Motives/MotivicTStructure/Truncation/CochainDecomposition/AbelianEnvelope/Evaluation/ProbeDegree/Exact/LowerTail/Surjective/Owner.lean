import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.LowerTail.Owner

/-!
# Lower-tail exactness from surjectivity

This file converts ordinary surjectivity of the first evaluated Q-module map
into exactness on normalized lower-tail degrees.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Surjectivity of the first evaluated map proves exactness on a normalized
lower-tail degree. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_surjective_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (hsurjective :
      Function.Surjective
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_range_top
    cut
    complex
    probe
    lowerTail
    ((LinearMap.range_eq_top).mpr hsurjective)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
