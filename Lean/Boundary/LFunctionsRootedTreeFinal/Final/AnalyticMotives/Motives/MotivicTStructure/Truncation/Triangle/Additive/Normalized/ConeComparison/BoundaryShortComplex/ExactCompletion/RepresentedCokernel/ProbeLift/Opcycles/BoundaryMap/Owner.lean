import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.AbelianEnvelope.Owner

/-!
# Represented opcycles boundary map normal form

This file identifies the represented boundary map before evaluating at a
probe: it is the Yoneda image of the genuine analytic opcycles projection,
transported through the boundary truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The represented boundary map is the Yoneda image of `pOpcycles` followed
by the inverse boundary truncation isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_opcycles_normalForm
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            htail
            hboundary).inv) :=
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g
        cut
        complex
        tail
        htail
        hboundary)
    (congrArg
      (fun morphism =>
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map morphism)
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap_inr_f_of_boundary
          cut
          complex
          tail
          cut
          htail
          hboundary))

/-- The represented boundary map factors as the represented opcycles projection
followed by the represented inverse boundary truncation isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_opcycles_factor
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g =
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.pOpcycles cut) ≫
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          htail
          hboundary).inv) :=
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_opcycles_normalForm
        cut
        complex
        tail
        htail
        hboundary)
    (Eq.symm
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_comp
        (complex.pOpcycles cut)
        ((_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          htail
          hboundary).inv)))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
