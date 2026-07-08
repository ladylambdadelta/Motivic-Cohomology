import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Owner

/-!
# Concrete probe lifts for the represented opcycles boundary

This file rewrites probewise surjectivity of the represented boundary map as
the concrete analytic statement that every probe morphism into the represented
opcycles boundary has a lift through the boundary projection.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Concrete probe lifts through the represented boundary map imply
probewise surjectivity of that map. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_probe_surjective_of_concrete_lifts
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
    (hlift :
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
            target) :
    ∀ probe : TraceAnalyticAdditiveCategoryObject,
      Function.Surjective
        ((TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g.app
          (Opposite.op probe)) :=
  fun probe target =>
    hlift probe target

/-- Probe exactness plus concrete probe lifts makes the exact-completion
comparison to the represented opcycles boundary an isomorphism. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_concrete_probe_lifts
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
    (hevaluation :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
            cut
            complex
            tail
            htail
            hboundary
            probe).Exact)
    (hlift :
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_probe_surjective
      cut
      complex
      tail
      htail
      hboundary
      hevaluation
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_probe_surjective_of_concrete_lifts
          cut
          complex
          tail
          htail
          hboundary
          hlift)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
