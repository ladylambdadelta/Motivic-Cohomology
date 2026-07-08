import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.FieldShape.Owner

/-!
# Boundary handoff for concrete Yoneda truncation representatives

This file attaches the represented opcycles boundary calculation to a concrete
Yoneda truncation representative.  The representative supplies the truncation
triangle from its degreewise exact analytic truncation sequence; the additional
boundary hypotheses identify the exact-completion boundary cokernel with the
represented opcycles boundary.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace YonedaTruncationRepresentative

/-- A concrete Yoneda truncation representative, together with the represented
opcycles boundary calculation for its representing complex, gives both the
exact-completion cokernel identification and the represented object's
field-order truncation triangle. -/
theorem boundaryHandoff_exists_object_truncation_triangle_fieldShape
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      IsSplitEpi (representative.complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
      representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE cut representative.complex).X cut),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            cut
            representative.complex
            tail
            htail
            hboundary) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ :
          TraceAnalyticDerivedMotiveCategory.HomologicalLE
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
        (firstMap : lower ⟶ object)
        (secondMap : object ⟶ upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  exact
    And.intro
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcycles
          cut
          representative.complex
          opcyclesSplit
          tail
          htail
          hboundary
          hrange)
      (TraceAnalyticMotivicTStructure
        .hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
          cut
          object
          (Nonempty.intro representative))

/-- The exact-completion boundary cokernel of a concrete Yoneda truncation
representative is the literal represented opcycles boundary. -/
theorem boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      IsSplitEpi (representative.complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
      representative.hasHomology
    ∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (representative.complex.opcycles cut),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              cut
              representative.complex
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
                  representative.complex
                  tail
                  htail
                  hboundary)) :=
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonBoundary_exactCompletionIsoRepresentedOpcyclesBoundary
      cut
      representative.complex
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- A concrete Yoneda truncation representative gives its field-order
truncation triangle together with the literal represented opcycles boundary
identification. -/
theorem boundaryHandoff_literalOpcycles_exists_object_truncation_triangle_fieldShape
    {cut : ℤ}
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative cut object)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      IsSplitEpi (representative.complex.pOpcycles cut))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).f tail =
        cut)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding cut).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                cut
                representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
      representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            cut
            representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (representative.complex.opcycles cut),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              cut
              representative.complex
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
                  representative.complex
                  tail
                  htail
                  hboundary))) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ :
          TraceAnalyticDerivedMotiveCategory.HomologicalLE
            (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
            lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE cut upper)
        (firstMap : lower ⟶ object)
        (secondMap : object ⟶ upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  exact
    And.intro
      (representative.boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)
      (TraceAnalyticMotivicTStructure
        .hasYonedaTruncationRepresentative_exists_object_truncation_triangle_fieldShape
          cut
          object
          (Nonempty.intro representative))

/-- The adjacent `≤ 0`, `≥ 1` specialization of the boundary handoff for a
concrete Yoneda truncation representative. -/
theorem boundaryHandoff_exists_triangle_zero_one_fieldShape
    {object : TraceAnalyticDerivedMotiveCategory}
    (representative :
      TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative 1 object)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      IsSplitEpi (representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
        representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
      representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE 1 representative.complex).X 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            representative.complex
            tail
            htail
            hboundary) ∧
      ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
        (firstMap : lower ⟶ object)
        (secondMap : object ⟶ upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ, representative.complex.HasHomology degree :=
    representative.hasHomology
  exact
    representative.boundaryHandoff_exists_object_truncation_triangle_fieldShape
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

end YonedaTruncationRepresentative

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
