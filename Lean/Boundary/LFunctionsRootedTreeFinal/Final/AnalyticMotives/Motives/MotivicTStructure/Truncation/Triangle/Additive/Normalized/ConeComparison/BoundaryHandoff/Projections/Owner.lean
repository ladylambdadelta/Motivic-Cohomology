import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Owner

/-!
# Projections from the normalized boundary handoff

This file exposes the two concrete consequences of the normalized
cone-comparison boundary handoff separately: the exact-completion cokernel
identification with the represented opcycles boundary, and represented
boundary short-complex exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The boundary handoff gives the canonical identification of the
exact-completion cokernel with the represented opcycles boundary. -/
theorem additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcycles
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
  TraceAnalyticMotivicTStructure
    .exactCompletionNormalizedConeComparisonBoundaryCokernel_eq_representedOpcyclesBoundary
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- At the boundary degree itself, the upper truncation object is the represented
opcycles object. -/
theorem additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail) :
    (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X cut =
      complex.opcycles cut :=
  TraceAnalyticMotivicTStructure.additiveTruncGE_X_of_boundary
    cut
    complex
    cut
    tail
    (ComplexShape.Embedding.r_eq_some
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut)
      htail)
    hboundary

/-- The boundary handoff identifies the exact-completion cokernel with the
literal represented opcycles boundary object. -/
theorem additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcyclesBoundary
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
          (complex.opcycles cut),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              cut
              complex
              tail
              htail
              hboundary ≫
          eqToHom
            (congrArg
              (fun object =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
                  cut
                  complex
                  tail
                  htail
                  hboundary)) :=
  let boundaryObjectEq :
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X cut =
        complex.opcycles cut :=
    TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
        cut
        complex
        tail
        htail
        hboundary
  let representedObjectEq :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) =
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.opcycles cut) :=
    congrArg
      (fun object =>
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
      boundaryObjectEq
  let boundaryPackage :
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
    TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcycles
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
  Exists.elim
    boundaryPackage
    (fun boundaryIso boundaryIso_hom =>
      Exists.intro
        (boundaryIso ≪≫ eqToIso representedObjectEq)
        (Eq.trans
          (Iso.trans_hom boundaryIso (eqToIso representedObjectEq))
          (congrArg
            (fun map => map ≫ eqToHom representedObjectEq)
            boundaryIso_hom)))

/-- The boundary handoff gives exactness of the represented normalized
boundary short complex. -/
theorem additiveNormalizedConeComparisonBoundary_representedShortComplex_exact
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
  (TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcycles_and_exact
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      hrange).right

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
