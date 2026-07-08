import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Projections.Owner

/-!
# Projections from the current field-order boundary handoff

This file exposes the boundary-identification part and the individual
constructor-order t-structure fields carried by the current field-order
boundary handoff certificate.
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

/-- The current field-order boundary handoff gives the exact-completion
boundary cokernel identification. -/
theorem current_full_constructor_order_boundaryHandoff_iso
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
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE 1 represented.representative.complex).X 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            represented.representative.complex
            tail
            htail
            hboundary := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (represented.current_full_constructor_order_boundaryHandoff_certificate
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).left

/-- The current field-order boundary handoff gives the literal represented
opcycles boundary identification. -/
theorem current_full_constructor_order_boundaryHandoff_literalOpcyclesIso_projection
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
    represented.current_full_constructor_order_boundaryHandoff_literalOpcyclesIso
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact

/-- The current field-order boundary handoff identifies the exact-completion
comparison map with an isomorphism onto the represented boundary object. -/
theorem current_full_constructor_order_boundaryHandoff_comparison_isIso
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
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          1
          represented.representative.complex
          tail
          htail
          hboundary) := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    represented.chosen_boundaryHandoff_exactCompletionBoundaryToRepresented_isIso
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- The current field-order boundary handoff identifies the transported
comparison map with an isomorphism onto the literal represented opcycles
boundary object. -/
theorem current_full_constructor_order_boundaryHandoff_literalComparison_isIso
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
    IsIso
      (TraceAnalyticMotivicTStructure
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
                hboundary))) := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    represented.chosen_boundaryHandoff_literalOpcyclesComparison_isIso
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- The current field-order boundary handoff pairs the literal represented
opcycles boundary identification with the constructor-order fields. -/
theorem current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate_projection
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
    represented.current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact

/-- The current field-order boundary handoff gives the constructor-order
t-structure-facing certificate. -/
theorem current_full_constructor_order_boundaryHandoff_fields
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
    (represented.current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).right

/-- The boundary handoff certificate gives adjacent monotonicity of the
analytic aisle predicate. -/
theorem current_full_constructor_order_boundaryHandoff_tStructureLE_zero_le
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
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (represented.current_full_constructor_order_boundaryHandoff_fields
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).left

/-- The boundary handoff certificate gives adjacent monotonicity of the
analytic coaisle predicate. -/
theorem current_full_constructor_order_boundaryHandoff_tStructureGE_one_le
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
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (represented.current_full_constructor_order_boundaryHandoff_fields
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).right.left

/-- The boundary handoff certificate gives adjacent truncation triangle
existence. -/
theorem current_full_constructor_order_boundaryHandoff_truncation_triangle
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
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (represented.current_full_constructor_order_boundaryHandoff_fields
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).right.right.left

/-- The boundary handoff certificate gives represented-object
orthogonality. -/
theorem current_full_constructor_order_boundaryHandoff_represented_firstMap_secondMap
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
    represented.firstMap ≫ represented.secondMap = 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (represented.current_full_constructor_order_boundaryHandoff_fields
      object
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hshortExact).right.right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
