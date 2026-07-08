import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Componentwise.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.EpiMono.ModuleCat.Owner

/-!
# Cochain short exactness from concrete probe-degree linear algebra

This file composes the componentwise truncation short-exact assembly theorem
with the `ModuleCat Rat` injective/surjective-to-mono/epi criteria.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness, ordinary injectivity of every named probe-degree
lower map, and ordinary surjectivity of every named probe-degree upper map
assemble to cochain-level short exactness for the actual Yoneda abelian-envelope
truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_probe_injective_surjective
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    (hinjective :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Function.Injective
            (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).f)
    (hsurjective :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Function.Surjective
            (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
    cut
    complex
    hexact
    (fun degree probe =>
      abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_injective
        cut
        complex
        probe
        degree
        (hinjective degree probe))
    (fun degree probe =>
      abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_surjective
        cut
        complex
        probe
        degree
        (hsurjective degree probe))

/-- Degreewise exactness, isomorphism of every named probe-degree lower map,
and isomorphism of every named probe-degree upper map assemble to cochain-level
short exactness for the actual Yoneda abelian-envelope truncation short complex.
-/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_probe_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).Exact)
    [∀ degree : ℤ,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        IsIso
          (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).f]
    [∀ degree : ℤ,
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        IsIso
          (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
            cut
            complex
            probe
            degree).g] :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
    cut
    complex
    hexact
    (fun degree probe =>
      abelianEnvelopeCochainDecompositionProbeDegreeMono_f_of_isIso
        cut
        complex
        probe
        degree)
    (fun degree probe =>
      abelianEnvelopeCochainDecompositionProbeDegreeEpi_g_of_isIso
        cut
        complex
        probe
        degree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
