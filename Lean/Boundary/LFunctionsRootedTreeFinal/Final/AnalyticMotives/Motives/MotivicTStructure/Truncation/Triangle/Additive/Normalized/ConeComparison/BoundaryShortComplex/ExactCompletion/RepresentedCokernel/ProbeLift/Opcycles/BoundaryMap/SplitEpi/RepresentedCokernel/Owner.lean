import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeExact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.BoundaryMap.SplitEpi.Owner

/-!
# Represented cokernel from split-epic analytic opcycles projection

This file feeds the direct represented-boundary epicity theorem into the
represented cokernel comparison.  The represented boundary is a cokernel once
its probe evaluations are exact and the analytic opcycles projection is
split-epic.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- Probe exactness plus split-epic analytic opcycles projection proves that
the represented opcycles boundary map is the cokernel of the represented
incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_boundaryMap_splitEpi
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
    (hevaluation :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
            cut
            complex
            tail
            htail
            hboundary
            probe).Exact) :
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
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_epi
      cut
      complex
      tail
      htail
      hboundary
      hevaluation
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_opcycles_isSplitEpi
          cut
          complex
          opcyclesSplit
          tail
          htail
          hboundary)

/-- Probe exactness plus split-epic analytic opcycles projection identifies
the exact-completion cokernel with the represented opcycles boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_boundaryMap_splitEpi
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
    (hevaluation :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
            cut
            complex
            tail
            htail
            hboundary
            probe).Exact) :
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
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_opcycles_isSplitEpi
          cut
          complex
          opcyclesSplit
          tail
          htail
          hboundary)

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection proves that the represented opcycles boundary map is the cokernel
of the represented incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_probe_range_eq_ker_boundaryMap_splitEpi
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
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_boundaryMap_splitEpi
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      (fun probe =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_of_range_eq_ker
            cut
            complex
            tail
            htail
            hboundary
            probe
            (hrange probe))

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection identifies the exact-completion cokernel with the represented
opcycles boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_boundaryMap_splitEpi
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
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary) :=
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_boundaryMap_splitEpi
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      (fun probe =>
        TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_of_range_eq_ker
            cut
            complex
            tail
            htail
            hboundary
            probe
            (hrange probe))

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection gives the canonical identification of the exact-completion
cokernel object with the represented opcycles boundary object. -/
def exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_of_probe_range_eq_ker_boundaryMap_splitEpi
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
    TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryCokernel
          cut
          complex ≅
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
        ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
          cut) :=
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOfIsCokernel
      cut
      complex
      tail
      htail
      hboundary
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_probe_range_eq_ker_boundaryMap_splitEpi
          cut
          complex
          opcyclesSplit
          tail
          htail
          hboundary
          hrange)

/-- The canonical identification of the exact-completion cokernel with the
represented opcycles boundary has the exact-completion comparison as its
forward map. -/
theorem exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_hom_of_probe_range_eq_ker_boundaryMap_splitEpi
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
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_of_probe_range_eq_ker_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange).hom =
      TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary :=
  rfl

/-- The exact-completion cokernel object is canonically the represented
opcycles boundary object.  The forward map of the displayed isomorphism is the
exact-completion comparison map. -/
theorem exactCompletionNormalizedConeComparisonBoundaryCokernel_eq_representedOpcyclesBoundary
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
    ∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary :=
  Exists.intro
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_of_probe_range_eq_ker_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)
    (TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_hom_of_probe_range_eq_ker_boundaryMap_splitEpi
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
