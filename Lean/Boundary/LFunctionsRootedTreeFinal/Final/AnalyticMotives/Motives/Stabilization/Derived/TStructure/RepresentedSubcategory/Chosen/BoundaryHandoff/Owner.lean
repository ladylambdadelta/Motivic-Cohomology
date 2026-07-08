import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Existence.Represented.Yoneda.Class.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.Certificate.Owner

/-!
# Boundary handoff for chosen represented truncation objects

This file attaches the represented opcycles boundary calculation to the
chosen cut-`1` representative of an object in the represented truncation
subcategory, while retaining the existing normalized triangle and short-complex
certificate.
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

/-- A represented truncation object whose chosen representative satisfies the
represented opcycles boundary hypotheses carries both the exact-completion
boundary cokernel identification and the normalized truncation certificate. -/
theorem chosen_boundaryHandoff_normalized_truncation_certificate
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            object.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE 1 object.representative.complex).X 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            object.representative.complex
            tail
            htail
            hboundary) ∧
      (object.representative.lowerObject =
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            0).obj object.lowerAisleObjectZero ∧
        object.representative.upperObject =
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
            1).obj object.upperCoaisleObjectOne ∧
          object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory ∧
            object.firstMap ≫ object.secondMap = 0 ∧
              object.secondMap ≫ object.connectingMap = 0 ∧
                object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0) ∧
        object.shortComplex.X₁ =
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            0).obj object.lowerAisleObjectZero ∧
          object.shortComplex.X₂ = object.object ∧
            object.shortComplex.X₃ =
              (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
                1).obj object.upperCoaisleObjectOne ∧
              object.shortComplex.f = object.firstMap ∧
                object.shortComplex.g = object.secondMap ∧
                  object.shortComplex.zero = object.firstMap_comp_secondMap ∧
                    (object.shortComplex.map
                        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                      (object.shortComplex.op.map
                        (preadditiveYoneda.obj rightProbe)).Exact := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    And.intro
      (TraceAnalyticMotivicTStructure
        .YonedaTruncationRepresentative
        .boundaryHandoff_exists_triangle_zero_one_fieldShape
          object.representative
          opcyclesSplit
          tail
          htail
          hboundary
          hrange).left
      (object.normalized_truncation_certificate leftProbe rightProbe)

/-- The chosen representative boundary handoff with the literal represented
opcycles boundary object, paired with the normalized truncation certificate. -/
theorem chosen_boundaryHandoff_literalOpcycles_normalized_truncation_certificate
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    (∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            object.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (object.representative.complex.opcycles 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              1
              object.representative.complex
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
                  object.representative.complex
                  tail
                  htail
                  hboundary))) ∧
      (object.representative.lowerObject =
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            0).obj object.lowerAisleObjectZero ∧
        object.representative.upperObject =
          (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
            1).obj object.upperCoaisleObjectOne ∧
          object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory ∧
            object.firstMap ≫ object.secondMap = 0 ∧
              object.secondMap ≫ object.connectingMap = 0 ∧
                object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0) ∧
        object.shortComplex.X₁ =
          (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
            0).obj object.lowerAisleObjectZero ∧
          object.shortComplex.X₂ = object.object ∧
            object.shortComplex.X₃ =
              (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
                1).obj object.upperCoaisleObjectOne ∧
              object.shortComplex.f = object.firstMap ∧
                object.shortComplex.g = object.secondMap ∧
                  object.shortComplex.zero = object.firstMap_comp_secondMap ∧
                    (object.shortComplex.map
                        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                      (object.shortComplex.op.map
                        (preadditiveYoneda.obj rightProbe)).Exact := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    And.intro
      (object.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)
      (object.normalized_truncation_certificate leftProbe rightProbe)

/-- Projection of the exact-completion boundary cokernel identification from
the chosen represented-object boundary handoff certificate. -/
theorem chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcycles
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    ∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            object.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          ((TraceAnalyticMotivicTStructure
            .additiveTruncGE 1 object.representative.complex).X 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryToRepresented
            1
            object.representative.complex
            tail
            htail
            hboundary := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    (TraceAnalyticMotivicTStructure
      .YonedaTruncationRepresentative
      .boundaryHandoff_exists_triangle_zero_one_fieldShape
        object.representative
        opcyclesSplit
        tail
        htail
        hboundary
        hrange).left

/-- Projection of the literal represented opcycles boundary identification from
the chosen represented-object boundary handoff certificate. -/
theorem chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (opcyclesSplit :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail : ℕ)
    (htail :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f tail =
        1)
    (hboundary :
      (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
        tail)
    (hrange :
      letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
        object.representative.hasHomology
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        LinearMap.range
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).f =
          LinearMap.ker
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                1
                object.representative.complex
                tail
                htail
                hboundary
                probe).g) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    ∃ boundaryIso :
      TraceAnalyticMotivicTStructure
          .exactCompletionNormalizedConeComparisonBoundaryCokernel
            1
            object.representative.complex ≅
        (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj
          (object.representative.complex.opcycles 1),
      boundaryIso.hom =
        TraceAnalyticMotivicTStructure
            .exactCompletionNormalizedConeComparisonBoundaryToRepresented
              1
              object.representative.complex
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
                  object.representative.complex
                  tail
                  htail
                  hboundary)) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    TraceAnalyticMotivicTStructure
      .YonedaTruncationRepresentative
      .boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
        object.representative
        opcyclesSplit
        tail
        htail
        hboundary
        hrange

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
