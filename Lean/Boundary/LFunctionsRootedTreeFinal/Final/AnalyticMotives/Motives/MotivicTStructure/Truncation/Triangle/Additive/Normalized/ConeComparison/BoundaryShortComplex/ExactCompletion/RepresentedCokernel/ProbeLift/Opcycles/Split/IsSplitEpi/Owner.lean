import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.Split.Owner

/-!
# Split-epi opcycles projection and the represented boundary cokernel

This file repackages the concrete section theorem for `pOpcycles` using
Mathlib's standard `IsSplitEpi` structure.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- If the analytic opcycles projection is a split epimorphism, then it gives
concrete probe lifts through that projection. -/
theorem additiveOpcyclesBoundaryProjection_probe_lifts_of_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [IsSplitEpi (complex.pOpcycles cut)] :
    ∀ (probe : TraceAnalyticAdditiveCategoryObject)
      (target : probe ⟶ complex.opcycles cut),
      ∃ source : probe ⟶ complex.X cut,
        source ≫ complex.pOpcycles cut =
          target :=
  TraceAnalyticMotivicTStructure
    .additiveOpcyclesBoundaryProjection_probe_lifts_of_section
      cut
      complex
      (section_ (complex.pOpcycles cut))
      (IsSplitEpi.id (complex.pOpcycles cut))

/-- Concrete probe range-kernel exactness plus split-epic opcycles projection
proves that the represented opcycles boundary map is the cokernel of the
represented incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_probe_range_eq_ker_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsSplitEpi (complex.pOpcycles cut)]
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
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_probe_range_eq_ker_opcycles_section
      cut
      complex
      tail
      htail
      hboundary
      (section_ (complex.pOpcycles cut))
      (IsSplitEpi.id (complex.pOpcycles cut))
      hrange

/-- Probe exactness plus split-epic opcycles projection proves that the
represented opcycles boundary map is the cokernel of the represented incoming
differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsSplitEpi (complex.pOpcycles cut)]
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
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_opcycles_section
      cut
      complex
      tail
      htail
      hboundary
      (section_ (complex.pOpcycles cut))
      (IsSplitEpi.id (complex.pOpcycles cut))
      hevaluation

/-- Concrete probe range-kernel exactness plus split-epic opcycles projection
identifies the exact-completion cokernel with the represented opcycles
boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsSplitEpi (complex.pOpcycles cut)]
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_opcycles_section
      cut
      complex
      tail
      htail
      hboundary
      (section_ (complex.pOpcycles cut))
      (IsSplitEpi.id (complex.pOpcycles cut))
      hrange

/-- Probe exactness plus split-epic opcycles projection identifies the
exact-completion cokernel with the represented opcycles boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_opcycles_isSplitEpi
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsSplitEpi (complex.pOpcycles cut)]
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_opcycles_section
      cut
      complex
      tail
      htail
      hboundary
      (section_ (complex.pOpcycles cut))
      (IsSplitEpi.id (complex.pOpcycles cut))
      hevaluation

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
