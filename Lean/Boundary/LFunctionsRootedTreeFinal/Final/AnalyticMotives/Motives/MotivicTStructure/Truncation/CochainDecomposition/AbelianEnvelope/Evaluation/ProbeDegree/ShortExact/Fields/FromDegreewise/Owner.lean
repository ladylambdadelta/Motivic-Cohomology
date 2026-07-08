import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Evaluation.ProbeDegree.Exact.FromDegreewise.Owner

/-!
# Probe-degree short-exact fields from degreewise short exactness

This file extracts the exact, mono, and epi fields of the named probe-degree
Q-module short complex from degreewise short exactness of the Yoneda truncation
decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies exactness of every named probe-degree Q-module
truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_exact_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
      cut
      complex
      probe
      degree).Exact :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).exact

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies monicity of every named probe-degree lower map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_mono_f_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Mono
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).f :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).mono_f

/-- Degreewise short exactness of the Yoneda abelian-envelope truncation
decomposition implies epicity of every named probe-degree upper map. -/
theorem abelianEnvelopeCochainDecompositionProbeDegree_epi_g_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
            cut
            complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Epi
      (abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).g :=
  (abelianEnvelopeCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).epi_g

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
