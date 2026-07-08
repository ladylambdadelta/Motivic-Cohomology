import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.LowerTail.Surjective.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.OffLowerTail.Injective.Owner

/-!
# Exactness reductions from evaluated isomorphisms

The nonboundary truncation components are represented by truncation
isomorphisms.  This file records the `ModuleCat Rat` consequences needed by
the evaluated support exactness reductions.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- An isomorphism in `ModuleCat Rat` is injective as an ordinary function. -/
theorem moduleCat_injective_of_isIso
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    [IsIso map] :
    Function.Injective map :=
  (ModuleCat.toLinearEquiv (asIso map)).injective

/-- An isomorphism in `ModuleCat Rat` is surjective as an ordinary function. -/
theorem moduleCat_surjective_of_isIso
    {source target : ModuleCat Rat}
    (map : source ⟶ target)
    [IsIso map] :
    Function.Surjective map :=
  (ModuleCat.toLinearEquiv (asIso map)).surjective

/-- If the first evaluated map is an isomorphism, then the evaluated
truncation short complex is exact on a normalized lower-tail degree. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_isIso_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    [IsIso
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).f] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeLowerTailExact_of_surjective_f
    cut
    complex
    probe
    lowerTail
    (TraceAnalyticMotivicTStructure.moduleCat_surjective_of_isIso
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).f)

/-- If the second evaluated map is an isomorphism, then the evaluated
truncation short complex is exact outside the paired lower-tail embedding. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_isIso_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    [IsIso
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailExact_of_injective_g
    cut
    complex
    probe
    degree
    hnone
    (TraceAnalyticMotivicTStructure.moduleCat_injective_of_isIso
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
