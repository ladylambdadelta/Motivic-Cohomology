import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.BoundaryHandoff.Family.Owner

/-!
# Projections from the family current field-order boundary handoff

This file exposes the boundary-identification and constructor-field parts of
the represented-family current boundary handoff certificate.
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

/-- The family current boundary handoff gives the represented boundary
identification at each represented truncation object. -/
theorem family_current_full_constructor_order_boundaryHandoff_iso
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
            (tail represented)
            (htail represented)
            (hboundary represented) := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (family_current_full_constructor_order_boundaryHandoff_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object
      hshortExact
      represented).left

/-- The family current boundary handoff gives the literal represented opcycles
boundary identification at each represented truncation object. -/
theorem family_current_full_constructor_order_boundaryHandoff_literalOpcyclesIso
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
              (tail represented)
              (htail represented)
              (hboundary represented) ≫
          eqToHom
            (congrArg
              (fun object =>
                (TraceAnalyticAdditiveAbelianEnvelope.yoneda).obj object)
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonBoundary_truncGE_X_eq_opcycles
                  1
                  represented.representative.complex
                  (tail represented)
                  (htail represented)
                  (hboundary represented))) := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (family_current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object
      hshortExact
      represented).left

/-- The family current boundary handoff gives the constructor-order
t-structure-facing fields at each represented truncation object. -/
theorem family_current_full_constructor_order_boundaryHandoff_fields
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)))
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
    (family_current_full_constructor_order_boundaryHandoff_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object
      hshortExact
      represented).right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
