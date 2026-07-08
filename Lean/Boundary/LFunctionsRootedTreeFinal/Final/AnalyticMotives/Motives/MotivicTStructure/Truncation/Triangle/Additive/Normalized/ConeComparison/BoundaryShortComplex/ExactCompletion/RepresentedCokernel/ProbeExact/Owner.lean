import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Concrete.Owner

/-!
# Probe exactness for the represented opcycles boundary

This file converts concrete range-kernel identities for the represented
analytic opcycles boundary short complex into the probe exactness input needed
by the exact-completion comparison theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Exactness of the represented boundary short complex evaluated at a probe
is equivalent to equality between the range of the incoming map and the kernel
of the represented opcycles boundary projection. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_iff_range_eq_ker
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
        probe).Exact ↔
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
              probe).g :=
  ShortComplex.moduleCat_exact_iff_range_eq_ker
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe)

/-- Concrete range-kernel equality proves probe exactness for the represented
opcycles boundary short complex. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_of_range_eq_ker
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
    (probe : TraceAnalyticAdditiveCategoryObject)
    (hrange :
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
      .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
        cut
        complex
        tail
        htail
        hboundary
        probe).Exact :=
  (TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex_exact_iff_range_eq_ker
      cut
      complex
      tail
      htail
      hboundary
      probe).mpr
    hrange

/-- Concrete range-kernel equalities at all probes plus concrete probe lifts
make the exact-completion comparison to the represented opcycles boundary an
isomorphism. -/
theorem exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_concrete_lifts
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
    .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_evaluation_exact_concrete_probe_lifts
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
      hlift

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
