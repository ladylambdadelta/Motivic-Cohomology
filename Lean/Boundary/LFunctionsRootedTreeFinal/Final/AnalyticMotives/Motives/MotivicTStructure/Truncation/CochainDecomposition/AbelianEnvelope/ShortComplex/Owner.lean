import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.YonedaComplex.Owner

/-!
# Abelian-envelope short complex for the truncation decomposition

This file maps the concrete cochain truncation-decomposition short complex
through the degreewise analytic Yoneda embedding into the abelian presheaf
envelope.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The abelian-envelope image of the normalized cochain truncation
decomposition short complex. -/
def abelianEnvelopeCochainDecompositionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticAbelianCochainComplex :=
  (TraceAnalyticMotivicTStructure.additiveCochainDecompositionShortComplex
    cut
    complex).map
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplexFunctor

/-- The first object of the abelian-envelope short complex is the Yoneda image
of the paired lower truncation. -/
theorem abelianEnvelopeCochainDecompositionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex) :=
  rfl

/-- The middle object of the abelian-envelope short complex is the Yoneda image
of the original complex. -/
theorem abelianEnvelopeCochainDecompositionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        complex :=
  rfl

/-- The third object of the abelian-envelope short complex is the Yoneda image
of the upper truncation. -/
theorem abelianEnvelopeCochainDecompositionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainComplex
        (TraceAnalyticMotivicTStructure.additiveTruncGE
          cut
          complex) :=
  rfl

/-- The first map of the abelian-envelope short complex is the Yoneda image of
the paired lower inclusion. -/
theorem abelianEnvelopeCochainDecompositionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).f =
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap
        (TraceAnalyticMotivicTStructure.additiveCochainDecompositionLowerMap
          cut
          complex) :=
  rfl

/-- The second map of the abelian-envelope short complex is the Yoneda image of
the upper projection. -/
theorem abelianEnvelopeCochainDecompositionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.abelianEnvelopeCochainDecompositionShortComplex
      cut
      complex).g =
      TraceAnalyticAdditiveAbelianEnvelope.yonedaCochainMap
        (TraceAnalyticMotivicTStructure.additiveCochainDecompositionUpperMap
          cut
          complex) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
