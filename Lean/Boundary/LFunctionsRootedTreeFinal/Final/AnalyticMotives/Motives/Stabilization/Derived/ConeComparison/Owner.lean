import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.AbelianEnvelope.Exact.Owner

/-!
# Derived cone comparison for analytic truncation

This file records the derived-category consequence of the cochain-level short
exactness theorem for the Yoneda image of the analytic additive truncation
sequence.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

attribute [local instance]
  TraceAnalyticDerivedMotiveCategory.hasDerivedCategory

/-- The canonical mapping-cone descent map attached to the Yoneda image of the
analytic truncation short complex. -/
def abelianEnvelopeCochainDecompositionDescShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    CochainComplex.mappingCone
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).f ⟶
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortComplex cut complex).X₃ :=
  CochainComplex.mappingCone.descShortComplex
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionShortComplex cut complex)

/-- Short exactness of the Yoneda abelian-envelope truncation sequence makes
the canonical cone-to-upper map a quasi-isomorphism. -/
theorem abelianEnvelopeCochainDecompositionDescShortComplex_quasiIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    QuasiIso
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionDescShortComplex cut complex) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex hshortExact

/-- The derived analytic motive category inverts the canonical cone-to-upper
map attached to a short exact Yoneda truncation sequence. -/
theorem abelianEnvelopeCochainDecompositionDescShortComplex_derived_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex)) :
    IsIso
      (TraceAnalyticDerivedMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDescShortComplex cut complex)) :=
  letI quasiIsoInstance :
      QuasiIso
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDescShortComplex cut complex) :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDescShortComplex_quasiIso
        cut
        complex
        hshortExact
  TraceAnalyticDerivedMotiveCategory.mapOf_isIso_of_quasiIso
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeCochainDecompositionDescShortComplex cut complex)

/-- Degreewise short exactness of the Yoneda truncation sequence is enough to
make the canonical cone-to-upper map invertible in derived analytic motives. -/
theorem abelianEnvelopeCochainDecompositionDescShortComplex_derived_isIso_of_degreewise
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hdegree :
      ∀ degree : ℤ,
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionShortComplex cut complex).map
          (HomologicalComplex.eval
            TraceAnalyticAdditiveAbelianEnvelope
            (ComplexShape.up ℤ)
            degree)).ShortExact) :
    IsIso
      (TraceAnalyticDerivedMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeCochainDecompositionDescShortComplex cut complex)) :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeCochainDecompositionDescShortComplex_derived_isIso
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeCochainDecompositionShortExact_of_degreewise
          cut
          complex
          hdegree)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
