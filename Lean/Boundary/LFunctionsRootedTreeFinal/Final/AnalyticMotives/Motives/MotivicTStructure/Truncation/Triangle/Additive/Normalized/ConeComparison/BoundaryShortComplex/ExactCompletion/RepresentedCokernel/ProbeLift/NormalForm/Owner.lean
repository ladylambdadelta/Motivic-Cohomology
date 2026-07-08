import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeExact.Owner

/-!
# Normal form for the represented opcycles boundary probe map

The represented boundary map in the normalized cone comparison is the Yoneda
image of the genuine analytic opcycles quotient `pOpcycles`, transported by
the boundary truncation isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The evaluated represented boundary map is the Yoneda image of `pOpcycles`
followed by the inverse boundary truncation isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g_opcycles_normalForm
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).g =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.pOpcycles cut ≫
          (_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            htail
            hboundary).inv)).app
        (Opposite.op probe) :=
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g
        cut
        complex
        tail
        htail
        hboundary
        probe)
    (congrArg
      (fun morphism =>
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map morphism).app
          (Opposite.op probe))
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonCochainMap_inr_f_of_boundary
          cut
          complex
          tail
          cut
          htail
          hboundary))

/-- The evaluated represented boundary map factors as the evaluated Yoneda map
of `pOpcycles` followed by the evaluated Yoneda map of the inverse boundary
truncation isomorphism. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g_opcycles_factor
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).g =
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.pOpcycles cut)).app
        (Opposite.op probe) ≫
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        ((_root_.HomologicalComplex.truncGEXIsoOpcycles
          complex
          (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
          htail
          hboundary).inv)).app
        (Opposite.op probe) :=
  Eq.trans
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g_opcycles_normalForm
        cut
        complex
        tail
        htail
        hboundary
        probe)
    (congrArg
      (fun morphism => morphism.app (Opposite.op probe))
      (Eq.symm
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map_comp
          (complex.pOpcycles cut)
          ((_root_.HomologicalComplex.truncGEXIsoOpcycles
            complex
            (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
            htail
            hboundary).inv))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
