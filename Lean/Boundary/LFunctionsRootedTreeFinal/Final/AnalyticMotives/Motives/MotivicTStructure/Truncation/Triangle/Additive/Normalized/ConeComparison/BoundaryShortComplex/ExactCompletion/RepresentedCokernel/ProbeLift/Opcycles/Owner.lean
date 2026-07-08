import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.NormalForm.Owner

/-!
# Opcycles lifts for the represented boundary cokernel

This file turns the genuine analytic lift statement through `pOpcycles` into
the concrete represented-boundary lift statement needed by the exact-completion
cokernel comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Concrete lifts through the analytic opcycles projection give concrete
lifts through the represented boundary map. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_concrete_lifts_of_opcycles_lifts
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
    (hopcyclesLift :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject)
        (target : probe ⟶ complex.opcycles cut),
        ∃ source : probe ⟶ complex.X cut,
          source ≫ complex.pOpcycles cut =
            target) :
    ∀ (probe : TraceAnalyticAdditiveCategoryObject)
      (target :
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut)).obj
          (Opposite.op probe)),
      ∃ source :
        ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut)).obj
          (Opposite.op probe),
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g.app
          (Opposite.op probe)) source =
          target :=
  fun probe target =>
    let truncIso :=
      _root_.HomologicalComplex.truncGEXIsoOpcycles
        complex
        (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
        htail
        hboundary
    Exists.elim
      (hopcyclesLift probe (target ≫ truncIso.hom))
      (fun source hsource =>
        Exists.intro
          source
          (Eq.trans
            (congrArg
              (fun morphism => morphism source)
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_g_opcycles_factor
                  cut
                  complex
                  tail
                  htail
                  hboundary
                  probe))
            (Eq.trans
              (congrArg
                (fun morphism => morphism ≫ truncIso.inv)
                hsource)
              (Eq.trans
                (Category.assoc target truncIso.hom truncIso.inv)
                (Eq.trans
                  (congrArg
                    (fun morphism => target ≫ morphism)
                    truncIso.hom_inv_id)
                  (Category.comp_id target))))))

/-- Probe range-kernel exactness plus concrete lifts through the analytic
opcycles projection identify the exact-completion cokernel with the represented
opcycles boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_opcycles_lifts
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
    (hrange :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                complex
                tail
                htail
                hboundary
                probe).g)
    (hopcyclesLift :
      ∀ (probe : TraceAnalyticAdditiveCategoryObject)
        (target : probe ⟶ complex.opcycles cut),
        ∃ source : probe ⟶ complex.X cut,
          source ≫ complex.pOpcycles cut =
            target) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary) :=
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_concrete_lifts
      cut
      complex
      tail
      htail
      hboundary
      hrange
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_concrete_lifts_of_opcycles_lifts
          cut
          complex
          tail
          htail
          hboundary
          hopcyclesLift)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
