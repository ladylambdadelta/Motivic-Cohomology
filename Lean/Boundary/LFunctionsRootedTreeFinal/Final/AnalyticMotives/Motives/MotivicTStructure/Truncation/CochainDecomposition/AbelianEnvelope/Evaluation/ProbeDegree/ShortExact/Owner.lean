import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.EpiMono.ModuleCat.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.ShortExact.Fields.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Support.Owner

/-!
# Short exactness of probe-degree truncation short complexes

This file packages exactness, monicity of the lower map, and epicity of the
upper map into short exactness for the concrete `ModuleCat Rat` short complex
obtained by evaluating the Yoneda truncation sequence at one probe and degree.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Exactness plus mono/epi of the two named Q-module maps gives short
exactness of the named probe-degree truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_mono_epi
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
    (hmono :
      Mono
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f)
    (hepi :
      Epi
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
  ShortComplex.ShortExact.mk'
    hexact
    hmono
    hepi

/-- Exactness plus ordinary injectivity of the lower map and ordinary
surjectivity of the upper map gives short exactness of the named probe-degree
truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_injective_surjective
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
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_mono_epi
    cut
    complex
    probe
    degree
    hexact
    (abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_injective
      cut
      complex
      probe
      degree
      hinjective)
    (abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_surjective
      cut
      complex
      probe
      degree
      hsurjective)

/-- On a normalized lower-tail degree, exactness and monicity of the lower
map imply short exactness because the upper truncation object evaluates to
zero, so the upper map is epic. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeLowerTailShortExact_of_exact_mono_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (lowerTail : ℕ)
    (hexact :
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).Exact)
    (hmono :
      Mono
        (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          (cut - 1 - (lowerTail : ℤ))).f) :
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      (cut - 1 - (lowerTail : ℤ))).ShortExact :=
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_mono_epi
    cut
    complex
    probe
    (cut - 1 - (lowerTail : ℤ))
    hexact
    hmono
    (TraceAnalyticMotivicTStructure.moduleCat_epi_of_isZero_target
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₃_isZero_of_lowerTail
          cut
          complex
          probe
          lowerTail)
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        (cut - 1 - (lowerTail : ℤ))).g)

/-- Outside the paired lower-tail embedding, exactness and epicity of the upper
map imply short exactness because the lower truncation object evaluates to
zero, so the lower map is monic. -/
theorem abelianEnvelopeCochainDecompositionProbeDegreeOffLowerTailShortExact_of_exact_epi_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ)
    (hnone :
      (TraceAnalyticMotivicTStructure.truncLEEmbedding
        (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r degree =
        none)
    (hexact :
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact)
    (hepi :
      Epi
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
  abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_exact_mono_epi
    cut
    complex
    probe
    degree
    hexact
    (TraceAnalyticMotivicTStructure.moduleCat_mono_of_isZero_source
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex_X₁_isZero_of_lowerTail_none
          cut
          complex
          probe
          degree
          hnone)
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f)
    hepi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
