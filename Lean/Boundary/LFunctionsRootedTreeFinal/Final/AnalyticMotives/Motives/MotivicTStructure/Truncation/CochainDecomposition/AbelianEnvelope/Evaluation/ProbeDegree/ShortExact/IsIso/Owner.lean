import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.RangeKernel.Owner

/-!
# Probe-degree short exactness from isomorphism data

This file packages the nonboundary local endpoint: when the relevant evaluated
truncation maps are isomorphisms, their categorical mono/epi consequences
combine with exactness, or with the range-kernel exactness criterion, to give
short exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Exactness plus isomorphism of the two named Q-module maps gives short
exactness of the named probe-degree truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hexact :
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact)
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f]
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g] :
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_mono_epi
    cut
    complex
    probe
    degree
    hexact
    (abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_isIso
      cut
      complex
      probe
      degree)
    (abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_isIso
      cut
      complex
      probe
      degree)

/-- Range-kernel equality plus isomorphism of the two named Q-module maps gives
short exactness of the named probe-degree truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_range_eq_ker_isIso
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
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f]
    [IsIso
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g] :
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).ShortExact :=
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_isIso
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

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
