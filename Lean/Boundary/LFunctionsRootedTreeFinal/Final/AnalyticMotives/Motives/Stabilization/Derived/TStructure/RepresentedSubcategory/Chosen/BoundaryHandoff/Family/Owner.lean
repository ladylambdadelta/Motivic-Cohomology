import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.RepresentedSubcategory.Chosen.BoundaryHandoff.Projections.Owner

/-!
# Family boundary handoff for represented truncation objects

This file lifts the chosen represented-object boundary handoff to a family
surface over the represented truncation subcategory.
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

/-- A family of represented boundary handoff inputs identifies each
exact-completion boundary cokernel with the represented boundary object. -/
theorem family_boundaryHandoff_exactCompletionIsoRepresentedOpcycles
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
    object.chosen_boundaryHandoff_exactCompletionCokernel_eq_representedOpcyclesBoundary
      (opcyclesSplit object)
      (tail object)
      (htail object)
      (hboundary object)
      (hrange object)

/-- A family of represented boundary handoff inputs identifies each
exact-completion boundary cokernel with the literal represented opcycles
boundary. -/
theorem family_boundaryHandoff_exactCompletionIsoLiteralOpcycles
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
    object.chosen_boundaryHandoff_exactCompletionCokernel_eq_literalRepresentedOpcyclesBoundary
      (opcyclesSplit object)
      (tail object)
      (htail object)
      (hboundary object)
      (hrange object)

/-- A family of represented boundary handoff inputs gives, for every
represented truncation object, the transported exact-completion comparison
isomorphism together with the normalized truncation certificate. -/
theorem family_boundaryHandoff_literalComparison_isIso_normalized_certificate
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
    IsIso
        (TraceAnalyticMotivicTStructure
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
                  (hboundary object)))) ∧
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
      (object.chosen_boundaryHandoff_literalOpcyclesComparison_isIso
        (opcyclesSplit object)
        (tail object)
        (htail object)
        (hboundary object)
        (hrange object))
      (And.intro
        (object.chosen_boundaryHandoff_triangle_certificate
          (opcyclesSplit object)
          (tail object)
          (htail object)
          (hboundary object)
          (hrange object)
          leftProbe
          rightProbe)
        (object.chosen_boundaryHandoff_shortComplex_certificate
          (opcyclesSplit object)
          (tail object)
          (htail object)
          (hboundary object)
          (hrange object)
          leftProbe
          rightProbe))

/-- A family of represented boundary handoff inputs gives the transported
exact-completion comparison isomorphism for every represented truncation
object. -/
theorem family_boundaryHandoff_literalComparison_isIso
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
                (hboundary object)))) := by
  letI : ∀ degree : ℤ, object.representative.complex.HasHomology degree :=
    object.representative.hasHomology
  exact
    object.chosen_boundaryHandoff_literalOpcyclesComparison_isIso
      (opcyclesSplit object)
      (tail object)
      (htail object)
      (hboundary object)
      (hrange object)

/-- A family of represented boundary handoff inputs gives the untransported
exact-completion comparison isomorphism for every represented truncation
object. -/
theorem family_boundaryHandoff_comparison_isIso
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
    object.chosen_boundaryHandoff_exactCompletionBoundaryToRepresented_isIso
      (opcyclesSplit object)
      (tail object)
      (htail object)
      (hboundary object)
      (hrange object)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
