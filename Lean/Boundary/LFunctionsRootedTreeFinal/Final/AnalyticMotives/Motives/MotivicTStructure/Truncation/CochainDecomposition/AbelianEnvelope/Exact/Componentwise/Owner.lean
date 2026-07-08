import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.EpiMono.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Componentwise route to truncation short exactness

This file specializes the standard abelian exact/mono/epi recipe to the actual
Yoneda truncation decomposition, with monicity and epicity checked componentwise
in the presheaf abelian envelope.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness, componentwise monicity of the lower-inclusion map, and
componentwise epicity of the upper-projection map assemble to cochain-level
short exactness for the actual Yoneda abelian-envelope truncation short complex.
-/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_componentwise_mono_epi
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
    (hmono :
      ∀ degree : ℤ,
        ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
          Mono
            ((((abelianEnvelopeCochainDecompositionShortComplex
                cut
                complex).map
              (HomologicalComplex.eval
                TraceAnalyticAdditiveAbelianEnvelope
                (ComplexShape.up ℤ)
                degree)).f).app object))
    (hepi :
      ∀ degree : ℤ,
        ∀ object : Opposite TraceAnalyticAdditiveCategoryObject,
          Epi
            ((((abelianEnvelopeCochainDecompositionShortComplex
                cut
                complex).map
              (HomologicalComplex.eval
                TraceAnalyticAdditiveAbelianEnvelope
                (ComplexShape.up ℤ)
                degree)).g).app object)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_mono_epi
    cut
    complex
    hexact
    (fun degree =>
      TraceAnalyticAdditiveAbelianEnvelope.mono_of_componentwise_mono
        (((abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).f)
        (hmono degree))
    (fun degree =>
      TraceAnalyticAdditiveAbelianEnvelope.epi_of_componentwise_epi
        (((abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).g)
        (hepi degree))

/-- Degreewise exactness, monicity of every named probe-degree lower-inclusion
map, and epicity of every named probe-degree upper-projection map assemble to
cochain-level short exactness for the actual Yoneda abelian-envelope truncation
short complex. -/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
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
    (hmono :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Mono
            ((abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).f))
    (hepi :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).g)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_componentwise_mono_epi
    cut
    complex
    hexact
    (abelianEnvelopeCochainDecomposition_componentwiseMono_f_of_probeDegree
      cut
      complex
      hmono)
    (abelianEnvelopeCochainDecomposition_componentwiseEpi_g_of_probeDegree
      cut
      complex
      hepi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
