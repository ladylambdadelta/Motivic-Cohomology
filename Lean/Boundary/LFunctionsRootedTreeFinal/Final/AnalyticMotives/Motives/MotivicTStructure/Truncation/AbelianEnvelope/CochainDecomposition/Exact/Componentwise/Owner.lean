import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Exact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.Evaluation.ProbeDegree.EpiMono.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Componentwise exact assembly for the intrinsic abelian-envelope decomposition

This file converts objectwise mono and epi checks in the presheaf abelian
envelope into the cochain-level short exactness field for the intrinsic
normalized truncation-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise exactness, componentwise monicity of the lower-inclusion map, and
componentwise epicity of the upper-projection map assemble to cochain-level
short exactness for the intrinsic abelian-envelope normalized truncation
decomposition. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_componentwise_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
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
            ((((TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
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
            ((((TraceAnalyticMotivicTStructure
                .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                  cut
                  complex).map
              (HomologicalComplex.eval
                TraceAnalyticAdditiveAbelianEnvelope
                (ComplexShape.up ℤ)
                degree)).g).app object)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
    cut
    complex
    hexact
    (fun degree =>
      TraceAnalyticAdditiveAbelianEnvelope.mono_of_componentwise_mono
        (((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).f)
        (hmono degree))
    (fun degree =>
      TraceAnalyticAdditiveAbelianEnvelope.epi_of_componentwise_epi
        (((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
              cut
              complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).g)
        (hepi degree))

/-- Degreewise exactness, monicity of every named intrinsic probe-degree
lower-inclusion map, and epicity of every named intrinsic probe-degree
upper-projection map assemble to cochain-level short exactness for the
intrinsic abelian-envelope normalized truncation decomposition. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_probe_mono_epi
    (cut : ℤ)
    (complex : TraceAnalyticAbelianCochainComplex)
    (hexact :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
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
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).f))
    (hepi :
      ∀ degree : ℤ,
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          Epi
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_componentwise_mono_epi
    cut
    complex
    hexact
    (abelianEnvelopeIntrinsicCochainDecomposition_componentwiseMono_f_of_probeDegree
      cut
      complex
      hmono)
    (abelianEnvelopeIntrinsicCochainDecomposition_componentwiseEpi_g_of_probeDegree
      cut
      complex
      hepi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
