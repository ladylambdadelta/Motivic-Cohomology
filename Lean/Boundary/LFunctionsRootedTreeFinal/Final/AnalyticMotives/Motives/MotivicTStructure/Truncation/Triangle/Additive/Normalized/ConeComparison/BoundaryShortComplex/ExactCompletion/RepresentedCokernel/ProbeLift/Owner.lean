import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.EpiMono.Owner

/-!
# Probe lifts for the represented opcycles boundary projection

Epicity of the represented analytic opcycles boundary projection is exactly
probewise surjectivity in the Q-module presheaf envelope.  This file records
that conversion for the normalized cone boundary and feeds it into the
exact-completion comparison theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Probewise surjectivity of the represented opcycles boundary projection
assembles to epicity of that projection in the analytic abelian presheaf
envelope. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_probe_surjective
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
    (hsurjective :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Function.Surjective
          ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).g.app
            (Opposite.op probe))) :
    Epi
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
          cut
          complex
          tail
          htail
          hboundary).g :=
  TraceAnalyticAdditiveAbelianEnvelope.epi_of_componentwise_epi
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g
    (fun object =>
      match object with
      | Opposite.op probe =>
          (ModuleCat.epi_iff_surjective
            ((TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
                cut
                complex
                tail
                htail
                hboundary).g.app
              (Opposite.op probe))).mpr
            (hsurjective probe))

/-- Probe exactness plus probewise lift-surjectivity makes the
exact-completion comparison to the represented opcycles boundary an
isomorphism. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_probe_surjective
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
    (hsurjective :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        Function.Surjective
          ((TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
              cut
              complex
              tail
              htail
              hboundary).g.app
            (Opposite.op probe))) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary) :=
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_epi
      cut
      complex
      tail
      htail
      hboundary
      hevaluation
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_probe_surjective
          cut
          complex
          tail
          htail
          hboundary
          hsurjective)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
