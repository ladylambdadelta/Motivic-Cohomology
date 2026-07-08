import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.Exact.FromDegreewise.Owner

/-!
# Intrinsic probe-degree short-exact fields from degreewise short exactness

This file extracts the exact, mono, and epi fields of the named intrinsic
probe-degree Q-module short complex from degreewise short exactness of the
abelian-envelope normalized truncation decomposition.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
decomposition implies exactness of every named intrinsic probe-degree Q-module
short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_exact_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
        cut
        complex
        probe
        degree).Exact :=
  (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).exact

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
decomposition implies monicity of every named intrinsic probe-degree lower
map. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_mono_f_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Mono
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).f :=
  (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).mono_f

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
decomposition implies epicity of every named intrinsic probe-degree upper
map. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionProbeDegree_epi_g_of_degreewiseShortExact
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact)
    (probe : TraceAnalyticAdditiveCategoryObject)
    (degree : ℤ) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
          cut
          complex
          probe
          degree).g :=
  (abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortExact_of_degreewise
    cut
    complex
    hdegree
    probe
    degree).epi_g

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
