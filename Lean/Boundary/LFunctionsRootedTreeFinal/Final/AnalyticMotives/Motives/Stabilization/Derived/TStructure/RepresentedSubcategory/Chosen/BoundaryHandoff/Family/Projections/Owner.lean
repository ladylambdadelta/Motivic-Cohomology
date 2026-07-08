import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Family.Owner

/-!
# Projections from the family boundary handoff

This file exposes the triangle and short-complex parts of the represented
family boundary handoff certificate.
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

/-- Projection of the family exact-completion iso to the represented boundary
object. -/
theorem family_boundaryHandoff_exactCompletionIsoRepresentedOpcycles_projection
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
            (tail object)
            (htail object)
            (hboundary object) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    family_boundaryHandoff_exactCompletionIsoRepresentedOpcycles
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object

/-- Projection of the family exact-completion iso to the literal represented
opcycles boundary object. -/
theorem family_boundaryHandoff_exactCompletionIsoLiteralOpcycles_projection
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
              (tail object)
              (htail object)
              (hboundary object) ≫
          eqToHom
            (congrArg
              (fun object =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object))) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    family_boundaryHandoff_exactCompletionIsoLiteralOpcycles
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object

/-- The family boundary handoff gives the untransported exact-completion
comparison isomorphism for each represented truncation object. -/
theorem family_boundaryHandoff_comparison_isIso_projection
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
      object.representative.hasHomology
    IsIso
      (TraceAnalyticMotivicTStructure
        .exactCompletionNormalizedConeComparisonBoundaryToRepresented
          1
          object.representative.complex
          (tail object)
          (htail object)
          (hboundary object)) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    family_boundaryHandoff_comparison_isIso
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object

/-- The family boundary handoff gives the normalized triangle certificate for
each represented truncation object. -/
theorem family_boundaryHandoff_triangle_certificate
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
    (family_boundaryHandoff_literalComparison_isIso_normalized_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe
      object).right.left

/-- The family boundary handoff gives the normalized short-complex certificate
for each represented truncation object. -/
theorem family_boundaryHandoff_shortComplex_certificate
    (opcyclesSplit :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        IsSplitEpi (object.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail object) =
          1)
    (hboundary :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail object))
    (hrange :
      ∀ object :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            object.representative.complex.HasHomology degree :=
          object.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  object.representative.complex
                  (tail object)
                  (htail object)
                  (hboundary object)
                  probe).g)
    (leftProbe : TraceAnalyticDerivedMotiveCategoryᵒᵖ)
    (rightProbe : TraceAnalyticDerivedMotiveCategory)
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
    (family_boundaryHandoff_literalComparison_isIso_normalized_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      leftProbe
      rightProbe
      object).right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
