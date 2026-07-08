import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.BoundaryMap.SplitEpi.RepresentedCokernel.Owner

/-!
# Represented boundary exactness from exact-completion comparison

The exact-completion boundary sequence is exact by construction.  If the
canonical comparison from the exact-completion cokernel to the represented
analytic boundary object is an isomorphism, then the represented analytic
boundary sequence inherits the same cokernel exactness.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

namespace TraceAnalyticMotivicTStructure

/-- If the exact-completion boundary cokernel comparison is an isomorphism,
then the represented normalized-cone boundary component is a cokernel of the
represented incoming differential. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_exactCompletionComparison_isIso
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
    [IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary)] :
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
  let exactProjection :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) ⟶
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryProjection
        cut
        complex
  let representedProjection :
      (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (complex.X cut) ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).g
  let comparison :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex ⟶
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented
        cut
        complex
        tail
        htail
        hboundary
  let exactZero :
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
          (complex.d (cut - 1) cut)) ≫ exactProjection =
        0 :=
    cokernel.condition
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut))
  let transportedCokernel :
      IsColimit
        (CokernelCofork.ofπ
          (exactProjection ≫ (asIso comparison).hom)
          (Eq.trans
            (Category.assoc
              ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
                (complex.d (cut - 1) cut))
              exactProjection
              (asIso comparison).hom)
            (Eq.trans
              (congrArg
                (fun morphism => morphism ≫ (asIso comparison).hom)
                exactZero)
              (zero_comp (asIso comparison).hom)))) :=
    TraceAnalyticMotivicTStructure.cokernelCofork_isColimit_comp_iso
      ((TraceAnalyticAdditiveAbelianEnvelope.yoneda).map
        (complex.d (cut - 1) cut))
      exactProjection
      exactZero
      (asIso comparison)
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryProjection_isCokernel
          cut
          complex)
  let fac :
      exactProjection ≫ comparison = representedProjection :=
    Eq.trans
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented_fac
          cut
          complex
          tail
          htail
          hboundary)
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g
            cut
            complex
            tail
            htail
            hboundary))
  IsColimit.ofIsoColimit
    transportedCokernel
    (Cofork.ext
      (Iso.refl _)
      (Eq.trans
        fac
        (Eq.symm (Category.comp_id representedProjection))))

/-- If the exact-completion comparison is an isomorphism, the represented
analytic boundary short complex is exact in the analytic presheaf abelian
envelope. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_exactCompletionComparison_isIso
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
    [IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          cut
          complex
          tail
          htail
          hboundary)] :
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary).Exact :=
  let shortComplex :
      ShortComplex TraceAnalyticAdditiveAbelianEnvelope :=
    TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex
        cut
        complex
        tail
        htail
        hboundary
  letI :
      shortComplex.HasHomology :=
    CategoryWithHomology.hasHomology shortComplex
  ShortComplex.exact_of_g_is_cokernel
    (TraceAnalyticMotivicTStructure
      .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_g_isCokernel_of_exactCompletionComparison_isIso
        cut
        complex
        tail
        htail
        hboundary)

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection proves exactness of the represented analytic boundary short
complex, by first identifying the exact-completion cokernel with the
represented opcycles boundary. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_probe_range_eq_ker_boundaryMap_splitEpi
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
  let comparisonIso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary) :=
    comparisonIso
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_exactCompletionComparison_isIso
      cut
      complex
      tail
      htail
      hboundary

/-- Concrete probe range-kernel exactness plus split-epic analytic opcycles
projection proves represented boundary exactness through the canonical
identification of the exact-completion cokernel with the represented opcycles
boundary object. -/
theorem abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_boundaryIsoRepresentedOpcycles_probe_range_eq_ker_boundaryMap_splitEpi
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
  let boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE cut complex).X
            cut) :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_of_probe_range_eq_ker_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
  let boundaryIsoHom :
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary :=
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryIsoRepresentedOpcycles_hom_of_probe_range_eq_ker_boundaryMap_splitEpi
        cut
        complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
  let boundaryComparisonIso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary) :=
    Eq.subst
      (motive := fun comparison =>
        IsIso comparison)
      boundaryIsoHom
      boundaryIso.isIso_hom
  letI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            complex
            tail
            htail
            hboundary) :=
    boundaryComparisonIso
  TraceAnalyticMotivicTStructure
    .abelianEnvelopeNormalizedConeComparisonBoundaryShortComplex_exact_of_exactCompletionComparison_isIso
      cut
      complex
      tail
      htail
      hboundary

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
