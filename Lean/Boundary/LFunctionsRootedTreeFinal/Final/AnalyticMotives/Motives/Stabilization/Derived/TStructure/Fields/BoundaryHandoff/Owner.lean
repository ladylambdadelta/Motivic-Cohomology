import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Constructors.ProbeDegreeCasewise.Owner

/-!
# Derived field handoff from the represented opcycles boundary

This file attaches the normalized exact-completion cokernel calculation to the
represented field-order truncation triangle supplied by probe-degree analytic
exactness.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- Probe-degree analytic exactness, together with the concrete represented
opcycles boundary calculation, gives both the exact-completion cokernel
identification and the represented field-order truncation triangle. -/
theorem probeDegreeCasewise_boundaryHandoff_exists_object_truncation_triangle_fieldShape
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      IsSplitEpi (complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
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
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
    (∃ boundaryIso :
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
            hboundary) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ :
          TraceAnalyticDerivedMotiveCategory.HomologicalLE
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
        (firstMap :
          lower ⟶
            TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex))
        (secondMap :
          TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex) ⟶
            upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  exact
    And.intro
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcycles
          cut
          complex
          opcyclesSplit
          tail
          htail
          hboundary
          hrange)
      (TraceAnalyticMotivicTStructure
        .probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- Probe-degree analytic exactness, together with the concrete represented
opcycles boundary calculation, identifies the exact-completion cokernel with
the literal represented opcycles boundary. -/
theorem probeDegreeCasewise_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      IsSplitEpi (complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
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
    letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
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
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcyclesBoundary
      cut
      complex
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- Probe-degree analytic exactness gives the represented field-order
truncation triangle together with the literal represented opcycles boundary
identification. -/
theorem probeDegreeCasewise_boundaryHandoff_literalOpcycles_exists_object_truncation_triangle_fieldShape
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      IsSplitEpi (complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
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
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              (cut - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                (cut - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              cut
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                cut
                complex
                probe
                degree).g) :
    letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
    (∃ boundaryIso :
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
                  hboundary))) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ :
          TraceAnalyticDerivedMotiveCategory.HomologicalLE
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
        (firstMap :
          lower ⟶
            TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex))
        (secondMap :
          TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex) ⟶
            upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  exact
    And.intro
      (TraceAnalyticMotivicTStructure
        .probeDegreeCasewise_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
          cut
          complex
          hasHomology
          opcyclesSplit
          tail
          htail
          hboundary
          hrange)
      (TraceAnalyticMotivicTStructure
        .probeDegreeCasewise_exists_object_truncation_triangle_fieldShape
          cut
          complex
          hasHomology
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)

/-- At the adjacent `≤ 0`, `≥ 1` cut, the represented opcycles boundary
calculation is packaged with the represented field-order truncation triangle. -/
theorem probeDegreeCasewise_boundaryHandoff_exists_triangle_zero_one_fieldShape
    (complex : TraceAnalyticAdditiveCochainComplex)
    (hasHomology : ∀ degree : ℤ, complex.HasHomology degree)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      IsSplitEpi (complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                complex
                tail
                htail
                hboundary
                probe).g)
    (hlowerExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              (1 - 1 - (lowerTail : ℤ))).Exact)
    (hlowerMono :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                (1 - 1 - (lowerTail : ℤ))).f)
    (hoffExact :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
              1
              complex
              probe
              degree).Exact)
    (hoffEpi :
      letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeCochainDecompositionProbeDegreeShortComplex
                1
                complex
                probe
                degree).g) :
    letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure.additiveTruncGE 1 complex).X
            1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            complex
            tail
            htail
            hboundary) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
        (firstMap :
          lower ⟶
            TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex))
        (secondMap :
          TraceAnalyticDerivedMotiveCategory.objectOf
              (TraceAnalyticAdditiveAbelianEnvelope
                .yonedaCochainComplex complex) ⟶
            upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, complex.HasHomology degree := hasHomology
  exact
    TraceAnalyticMotivicTStructure
      .probeDegreeCasewise_boundaryHandoff_exists_object_truncation_triangle_fieldShape
        1
        complex
        hasHomology
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
