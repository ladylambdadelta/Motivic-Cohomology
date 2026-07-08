import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.BoundaryShortComplex.ExactCompletion.RepresentedCokernel.ProbeLift.Opcycles.BoundaryMap.SplitEpi.RepresentedCokernel.Owner

/-!
# Projections from the chosen represented-object boundary handoff

This file exposes the exact-completion boundary identification, normalized
triangle certificate, and normalized short-complex certificate as separate
fields of the chosen represented-object boundary handoff.
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

/-- The chosen boundary handoff certificate identifies the exact-completion
boundary cokernel with the represented opcycles boundary. -/
theorem chosen_boundaryHandoff_exactCompletionCokernel_eq_representedOpcyclesBoundary
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
    object.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcycles
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- The chosen boundary handoff certificate identifies the exact-completion
boundary cokernel with the literal represented opcycles boundary. -/
theorem chosen_boundaryHandoff_exactCompletionCokernel_eq_literalRepresentedOpcyclesBoundary
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
    object.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
      opcyclesSplit
      tail
      htail
      hboundary
      hrange

/-- The chosen boundary handoff identifies the exact-completion comparison map
with an isomorphism onto the represented boundary object. -/
theorem chosen_boundaryHandoff_exactCompletionBoundaryToRepresented_isIso
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
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          1
          object.representative.complex
          tail
          htail
          hboundary) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    TraceAnalyticMotivicTStructure
      .exactCompletionNormalizedConeComparisonBoundaryToRepresented_isIso_of_probe_range_eq_ker_boundaryMap_splitEpi
        1
        object.representative.complex
        opcyclesSplit
        tail
        htail
        hboundary
        hrange

/-- The chosen boundary handoff identifies the exact-completion comparison map,
transported along the normalized opcycles equality, with an isomorphism onto
the literal represented opcycles boundary object. -/
theorem chosen_boundaryHandoff_literalOpcyclesComparison_isIso
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
    IsIso
      (TraceAnalyticMotivicTStructure
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
                hboundary))) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    Exists.elim
      (object.chosen_boundaryHandoff_exactCompletionIsoRepresentedOpcyclesBoundary
        opcyclesSplit
        tail
        htail
        hboundary
        hrange)
      (fun boundaryIso boundaryIso_hom =>
        boundaryIso_hom ▸ boundaryIso.isIso_hom)

/-- The chosen boundary handoff certificate pairs the literal represented
opcycles boundary identification with the normalized certificate. -/
theorem chosen_boundaryHandoff_literalOpcycles_normalized_certificate
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
    object.chosen_boundaryHandoff_literalOpcycles_normalized_truncation_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe

/-- The chosen boundary handoff certificate gives the normalized triangle
certificate. -/
theorem chosen_boundaryHandoff_triangle_certificate
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
    object.representative.lowerObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalAisle.inclusion
          0).obj object.lowerAisleObjectZero ∧
      object.representative.upperObject =
        (TraceAnalyticDerivedMotiveCategory.HomologicalCoaisle.inclusion
          1).obj object.upperCoaisleObjectOne ∧
        object.triangle ∈ distTriang TraceAnalyticDerivedMotiveCategory ∧
          object.firstMap ≫ object.secondMap = 0 ∧
            object.secondMap ≫ object.connectingMap = 0 ∧
              object.connectingMap ≫ object.firstMap⟦(1 : ℤ)⟧' = 0 := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    (object.chosen_boundaryHandoff_literalOpcycles_normalized_truncation_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe).right.left

/-- The chosen boundary handoff certificate gives the normalized short-complex
certificate. -/
theorem chosen_boundaryHandoff_shortComplex_certificate
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
    (object.chosen_boundaryHandoff_literalOpcycles_normalized_truncation_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe).right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
