import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Owner

/-!
# Boundary handoff for the current field-order certificate

This file pairs the represented-object exact-completion boundary calculation
with the current constructor-order t-structure-facing field certificate.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated
open scoped CategoryTheory

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The chosen represented-object boundary handoff, paired with the current
constructor-order t-structure-facing fields. -/
theorem current_full_constructor_order_boundaryHandoff_certificate
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (opcyclesSplit :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      IsSplitEpi (represented.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).g)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            represented.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE 1 represented.representative.complex).X 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            represented.representative.complex
            tail
            htail
            hboundary) ∧
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
          TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
            TraceAnalyticDerivedMotiveCategory.tStructureGE 0 ∧
          (∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
            (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
            (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
            (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory) ∧
            represented.firstMap ≫ represented.secondMap = 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    And.intro
      (represented.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcycles
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)
      (represented.current_full_constructor_order_certificate
        object
        hshortExact)

/-- The current field-order boundary handoff also exposes the literal
represented opcycles boundary identification. -/
theorem current_full_constructor_order_boundaryHandoff_literalOpcyclesIso
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (opcyclesSplit :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      IsSplitEpi (represented.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).g)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    ∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            represented.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (represented.representative.complex.opcycles 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              1
              represented.representative.complex
              tail
              htail
              hboundary ≫
          eqToHom
            (congrArg
              (fun object =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
                  1
                  represented.representative.complex
                  tail
                  htail
                  hboundary)) := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    represented.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- The current field-order boundary handoff with the literal represented
opcycles boundary object, paired with the constructor-order fields. -/
theorem current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (opcyclesSplit :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      IsSplitEpi (represented.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ,
          represented.representative.complex.HasHomology degree :=
        represented.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                represented.representative.complex
                tail
                htail
                hboundary
                probe).g)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            represented.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (represented.representative.complex.opcycles 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              1
              represented.representative.complex
              tail
              htail
              hboundary ≫
          eqToHom
            (congrArg
              (fun object =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
                  1
                  represented.representative.complex
                  tail
                  htail
                  hboundary))) ∧
      TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
          TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
        TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
            TraceAnalyticDerivedMotiveCategory.tStructureGE 0 ∧
          (∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
            (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
            (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
            (firstMap : lower ⟶ object)
            (secondMap : object ⟶ upper)
            (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
            Triangle.mk firstMap secondMap connectingMap ∈
              distTriang TraceAnalyticDerivedMotiveCategory) ∧
            represented.firstMap ≫ represented.secondMap = 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    And.intro
      (represented.current_full_constructor_order_boundaryHandoff_literalOpcyclesIso
        object
        opcyclesSplit
        tail
        htail
        hboundary
        hrange
        hshortExact)
      (represented.current_full_constructor_order_certificate
        object
        hshortExact)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
