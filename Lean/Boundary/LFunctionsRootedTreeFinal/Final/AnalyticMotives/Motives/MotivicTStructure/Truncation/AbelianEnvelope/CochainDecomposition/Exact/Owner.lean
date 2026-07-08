import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.AbelianEnvelope.CochainDecomposition.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Owner

/-!
# Exact assembly for the intrinsic abelian-envelope truncation short complex

This file specializes the abelian-envelope cochain-complex exactness assembly
theorems to the intrinsic normalized truncation-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise short exactness of the intrinsic abelian-envelope truncation
short complex assembles to cochain-level short exactness. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise
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
            degree)).ShortExact) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  TraceAnalyticAbelianCochainComplex.shortExact_of_degreewise_shortExact
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)
    hdegree

/-- Degreewise exactness of the intrinsic abelian-envelope truncation short
complex assembles to cochain-level exactness. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionExact_of_degreewise
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
            degree)).Exact) :
    TraceAnalyticAbelianCochainComplex.exact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  TraceAnalyticAbelianCochainComplex.exact_of_degreewise_exact
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)
    hdegree

/-- Degreewise exactness, monicity of the lower-inclusion map, and epicity of
the upper-projection map assemble to cochain-level short exactness for the
intrinsic abelian-envelope truncation short complex. -/
theorem abelianEnvelopeIntrinsicCochainDecompositionShortExact_of_degreewise_exact_mono_epi
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
        Mono
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          (((TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
                cut
                complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
          cut
          complex) :=
  TraceAnalyticAbelianCochainComplex.shortExact_of_degreewise_exact_mono_epi
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeIntrinsicCochainDecompositionShortComplex cut complex)
    hexact
    hmono
    hepi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
