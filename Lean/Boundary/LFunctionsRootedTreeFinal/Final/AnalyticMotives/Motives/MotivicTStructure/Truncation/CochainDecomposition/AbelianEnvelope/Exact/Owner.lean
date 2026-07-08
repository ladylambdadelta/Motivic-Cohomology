import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Complexes.Exact.Owner

/-!
# Exact assembly target for the abelian-envelope truncation short complex

This file specializes the degreewise short-exact assembly theorem to the
Yoneda image of the concrete normalized truncation-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Degreewise short exactness of the abelian-envelope truncation short complex
assembles to cochain-level short exactness. -/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise
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
            degree)).ShortExact) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  TraceAnalyticAbelianCochainComplex.shortExact_of_degreewise_shortExact
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex)
    hdegree

/-- Degreewise exactness of the abelian-envelope truncation short complex
assembles to cochain-level exactness. -/
theorem abelianEnvelopeCochainDecompositionExact_of_degreewise
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
            degree)).Exact) :
    TraceAnalyticAbelianCochainComplex.exact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  TraceAnalyticAbelianCochainComplex.exact_of_degreewise_exact
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex)
    hdegree

/-- Degreewise exactness, monicity of the lower-inclusion map, and epicity of
the upper-projection map assemble to cochain-level short exactness for the
actual Yoneda abelian-envelope truncation short complex. -/
theorem abelianEnvelopeCochainDecompositionShortExact_of_degreewise_exact_mono_epi
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
        Mono
          (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).f))
    (hepi :
      ∀ degree : ℤ,
        Epi
          (((TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
              cut
              complex).map
            (HomologicalComplex.eval
              TraceAnalyticAdditiveAbelianEnvelope
              (ComplexShape.up ℤ)
              degree)).g)) :
    TraceAnalyticAbelianCochainComplex.shortExact
      (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
        cut
        complex) :=
  TraceAnalyticAbelianCochainComplex.shortExact_of_degreewise_exact_mono_epi
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex)
    hexact
    hmono
    hepi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
