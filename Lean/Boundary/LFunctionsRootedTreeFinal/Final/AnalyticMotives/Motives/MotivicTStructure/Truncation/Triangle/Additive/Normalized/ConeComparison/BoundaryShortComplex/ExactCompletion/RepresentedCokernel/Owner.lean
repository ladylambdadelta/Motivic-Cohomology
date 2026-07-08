import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.AbelianEnvelope.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.ComparisonIso.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.CollectiveEvaluation.Exact.Coordinates.Owner

/-!
# Represented boundary cokernel from probe exactness and epicity

The represented analytic opcycles boundary is a cokernel in the abelian
presheaf envelope once its short complex is exact and its boundary projection
is epic.  Exactness is assembled from ordinary probe evaluations; epicity is
the remaining analytic lift theorem for opcycles quotients.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- If every probe evaluation of the represented boundary short complex is
exact and the represented opcycles boundary projection is epic, then that
represented boundary projection is the cokernel of the represented incoming
differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_epi
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
    (hepi :
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g) :
    IsColimit
      (CokernelCofork.ofπ
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).zero) :=
  let shortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary
  let exactBoundary :
      shortComplex.Exact :=
    TraceAnalyticAdditiveAbelianEnvelope.exact_of_evaluation_exact
      shortComplex
      hevaluation
  haveI : Epi shortComplex.g := hepi
  exactBoundary.gIsCokernel

/-- Probe exactness together with epicity of the represented opcycles boundary
projection makes the exact-completion comparison map an isomorphism. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_epi
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
    (hepi :
      Epi
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
            cut
            complex
            tail
            htail
            hboundary).g) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary) :=
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_represented_isCokernel
      cut
      complex
      tail
      htail
      hboundary
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_epi
          cut
          complex
          tail
          htail
          hboundary
          hevaluation
          hepi)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
