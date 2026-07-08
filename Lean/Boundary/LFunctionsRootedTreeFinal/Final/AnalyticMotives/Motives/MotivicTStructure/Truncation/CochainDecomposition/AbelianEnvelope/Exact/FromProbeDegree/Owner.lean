import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.FromProbeDegree.Owner

/-!
# Cochain short exactness from probe-degree casewise exactness

This file assembles the concrete probe-degree truncation exactness calculus
into cochain-level short exactness for the analytic abelian-envelope truncation
sequence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Casewise probe-degree exactness plus the remaining mono/epi fields assemble
to cochain-level short exactness of the Yoneda abelian-envelope truncation
short complex. -/
theorem abelianEnvelopeCochainDecompositionShortExact_of_probeDegree_casewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionShortExact_of_degreewise
      cut
      complex
      (fun degree =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDegreeShortExact_of_probeDegree_casewise
            cut
            complex
            degree
            hlowerExact
            hlowerMono
            hoffExact
            hoffEpi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
