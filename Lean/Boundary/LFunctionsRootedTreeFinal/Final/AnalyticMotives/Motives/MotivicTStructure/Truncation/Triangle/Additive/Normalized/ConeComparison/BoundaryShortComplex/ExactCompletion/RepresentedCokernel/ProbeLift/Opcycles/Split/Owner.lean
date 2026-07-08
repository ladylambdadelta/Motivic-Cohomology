import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.Owner

/-!
# Split opcycles projection and the represented boundary cokernel

This file records the concrete split-projection route to the represented
boundary cokernel comparison.  A genuine section of `pOpcycles` gives probe
lifts by composition, and those lifts identify the exact-completion cokernel
with the represented opcycles boundary.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- A section of the analytic opcycles projection gives concrete probe lifts
through that projection. -/
theorem additiveOpcyclesBoundaryProjection_probe_lifts_of_section
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (section : complex.opcycles cut ⟶ complex.X cut)
    (hsection :
      section ≫ complex.pOpcycles cut =
        𝟙 (complex.opcycles cut)) :
    ∀ (probe : TraceAnalyticAdditiveCategoryObject)
      (target : probe ⟶ complex.opcycles cut),
      ∃ source : probe ⟶ complex.X cut,
        source ≫ complex.pOpcycles cut =
          target :=
  fun probe target =>
    Exists.intro
      (target ≫ section)
      (Eq.trans
        (Category.assoc target section (complex.pOpcycles cut))
        (Eq.trans
          (congrArg
            (fun morphism => target ≫ morphism)
            hsection)
          (Category.comp_id target)))

/-- Probe range-kernel exactness plus a section of the analytic opcycles
projection identifies the exact-completion cokernel with the represented
opcycles boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_opcycles_section
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
    (section : complex.opcycles cut ⟶ complex.X cut)
    (hsection :
      section ≫ complex.pOpcycles cut =
        𝟙 (complex.opcycles cut))
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_opcycles_lifts
      cut
      complex
      tail
      htail
      hboundary
      hrange
      (TraceAnalyticMotivicTStructure
        .additiveOpcyclesBoundaryProjection_probe_lifts_of_section
          cut
          complex
          section
          hsection)

/-- Concrete probe range-kernel exactness plus a section of the analytic
opcycles projection proves that the represented opcycles boundary map is the
cokernel of the represented incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_probe_range_eq_ker_opcycles_section
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
    (section : complex.opcycles cut ⟶ complex.X cut)
    (hsection :
      section ≫ complex.pOpcycles cut =
        𝟙 (complex.opcycles cut))
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
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_epi
      cut
      complex
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
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_probe_surjective
          cut
          complex
          tail
          htail
          hboundary
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_probe_surjective_of_concrete_lifts
              cut
              complex
              tail
              htail
              hboundary
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_concrete_lifts_of_opcycles_lifts
                  cut
                  complex
                  tail
                  htail
                  hboundary
                  (TraceAnalyticMotivicTStructure
                    .additiveOpcyclesBoundaryProjection_probe_lifts_of_section
                      cut
                      complex
                      section
                      hsection))))

/-- Probe exactness plus a section of the analytic opcycles projection proves
that the represented opcycles boundary map is the cokernel of the represented
incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_opcycles_section
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
    (section : complex.opcycles cut ⟶ complex.X cut)
    (hsection :
      section ≫ complex.pOpcycles cut =
        𝟙 (complex.opcycles cut))
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
      (CategoryTheory.Limits.CokernelCofork.ofπ
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
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_epi_of_probe_surjective
          cut
          complex
          tail
          htail
          hboundary
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_probe_surjective_of_concrete_lifts
              cut
              complex
              tail
              htail
              hboundary
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_concrete_lifts_of_opcycles_lifts
                  cut
                  complex
                  tail
                  htail
                  hboundary
                  (TraceAnalyticMotivicTStructure
                    .additiveOpcyclesBoundaryProjection_probe_lifts_of_section
                      cut
                      complex
                      section
                      hsection))))

/-- Probe exactness plus a section of the analytic opcycles projection
identifies the exact-completion cokernel with the represented opcycles
boundary. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_opcycles_section
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
    (section : complex.opcycles cut ⟶ complex.X cut)
    (hsection :
      section ≫ complex.pOpcycles cut =
        𝟙 (complex.opcycles cut))
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_represented_isCokernel
      cut
      complex
      tail
      htail
      hboundary
      (TraceAnalyticMotivicTStructure
        .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_evaluation_exact_opcycles_section
          cut
          complex
          tail
          htail
          hboundary
          section
          hsection
          hevaluation)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
