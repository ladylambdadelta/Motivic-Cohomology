import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.OffLowerTail.Owner

/-!
# Off-lower-tail exactness from injectivity

This file converts ordinary injectivity of the second evaluated Q-module map
into exactness outside the paired lower-tail embedding.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Injectivity of the second evaluated map proves exactness outside the paired
lower-tail embedding. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_injective_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hinjective :
      Function.Injective
        (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g) :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_ker_bot
    cut
    complex
    probe
    degree
    hnone
    ((LinearMap.ker_eq_bot).mpr hinjective)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
