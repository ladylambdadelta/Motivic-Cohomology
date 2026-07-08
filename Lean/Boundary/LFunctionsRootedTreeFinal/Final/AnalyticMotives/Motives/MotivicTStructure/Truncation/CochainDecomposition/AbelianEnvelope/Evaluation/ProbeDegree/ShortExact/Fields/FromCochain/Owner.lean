import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.FromCochain.Owner

/-!
# Probe-degree short-exact fields from cochain short exactness

This file extracts the exact, mono, and epi fields of the named probe-degree
Q-module short complex from cochain-level short exactness of the Yoneda
truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Cochain-level short exactness of the Yoneda abelian-envelope truncation
decomposition implies exactness of every named probe-degree Q-module
truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_exact_of_cochainShortExact
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
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    hshortExact).exact

/-- Cochain-level short exactness of the Yoneda abelian-envelope truncation
decomposition implies monicity of every named probe-degree lower map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_mono_f_of_cochainShortExact
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
    Mono
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    hshortExact).mono_f

/-- Cochain-level short exactness of the Yoneda abelian-envelope truncation
decomposition implies epicity of every named probe-degree upper map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_epi_g_of_cochainShortExact
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
    Epi
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_cochainShortExact
    cut
    complex
    probe
    degree
    hshortExact).epi_g

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
