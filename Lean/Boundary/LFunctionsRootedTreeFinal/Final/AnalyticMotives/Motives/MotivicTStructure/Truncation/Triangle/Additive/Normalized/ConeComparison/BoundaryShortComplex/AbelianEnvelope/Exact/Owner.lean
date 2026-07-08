import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.AbelianEnvelope.Exact.Evaluation.Owner

/-!
# Exactness of the represented normalized boundary short complex

This file is the canonical abelian-envelope exactness owner for the represented
boundary short complex of the normalized cone comparison.  The proof is the
exact-completion cokernel comparison specialized to the concrete analytic
range-kernel and split-epic opcycles hypotheses.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection proves exactness of the represented normalized boundary short
complex in the analytic abelian envelope. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_boundaryMap_splitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (opcyclesSplit : IsSplitEpi (complex.pOpcycles cut))
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
                probe).g) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).Exact :=
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_boundaryIsoRepresentedOpcycles_probe_range_eq_ker_boundaryMap_splitEpi
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection proves exactness after evaluating the represented normalized
boundary short complex at any analytic additive probe. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_of_boundaryMap_splitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (opcyclesSplit : IsSplitEpi (complex.pOpcycles cut))
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
    (probe : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).Exact :=
  TraceAnalyticAdditiveAbelianEnvelope.evaluation_exact
    probe
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
