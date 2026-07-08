import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.ProbeDegree.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.BoundaryHandoff.Family.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.Constructors.ProbeDegree.Owner

/-!
# Family probe-degree boundary handoff

This file combines represented-family boundary handoff data with probe-degree
exactness for the canonical cochain-preimage decomposition.
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

/-- Probe-degree exactness plus the represented-family boundary handoff gives,
at each represented object, the represented boundary identification and the
current constructor-order t-structure-facing fields. -/
theorem family_current_full_probeDegree_boundaryHandoff_certificate
    (opcyclesSplit :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            represented.representative.complex.HasHomology degree :=
          represented.representative.hasHomology
        IsSplitEpi (represented.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail represented) =
          1)
    (hboundary :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail represented))
    (hrange :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            represented.representative.complex.HasHomology degree :=
          represented.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  represented.representative.complex
                  (tail represented)
                  (htail represented)
                  (hboundary represented)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  represented.representative.complex
                  (tail represented)
                  (htail represented)
                  (hboundary represented)
                  probe).g)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
            (tail represented)
            (htail represented)
            (hboundary represented)) ∧
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
  let hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_shortExact_of_probeDegree_casewise
        object
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    family_current_full_constructor_order_boundaryHandoff_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object
      hshortExact
      represented

/-- Probe-degree exactness plus the represented-family boundary handoff gives,
at each represented object, the literal opcycles boundary identification and
the current constructor-order t-structure-facing fields. -/
theorem family_current_full_probeDegree_boundaryHandoff_literalOpcycles_certificate
    (opcyclesSplit :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            represented.representative.complex.HasHomology degree :=
          represented.representative.hasHomology
        IsSplitEpi (represented.representative.complex.pOpcycles 1))
    (tail :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject → ℕ)
    (htail :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).f
            (tail represented) =
          1)
    (hboundary :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        (TraceAnalyticMotivicTStructure.truncGEEmbedding 1).BoundaryGE
          (tail represented))
    (hrange :
      ∀ represented :
        TraceAnalyticMotivicTStructure.RepresentedTruncationObject,
        letI : ∀ degree : ℤ,
            represented.representative.complex.HasHomology degree :=
          represented.representative.hasHomology
        ∀ probe : TraceAnalyticAdditiveCategoryObject,
          LinearMap.range
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  represented.representative.complex
                  (tail represented)
                  (htail represented)
                  (hboundary represented)
                  probe).f =
            LinearMap.ker
              (TraceAnalyticMotivicTStructure
                .abelianEnvelopeNormalizedConeComparisonBoundaryProbeShortComplex
                  1
                  represented.representative.complex
                  (tail represented)
                  (htail represented)
                  (hboundary represented)
                  probe).g)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hlowerExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                (lowerTail : ℤ))).Exact)
    (hlowerMono :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ lowerTail : ℕ,
          Mono
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                (TraceAnalyticMotivicTStructure.decompositionLowerCut 1 -
                  (lowerTail : ℤ))).f)
    (hoffExact :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          (TraceAnalyticMotivicTStructure
            .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
              1
              (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
              probe
              degree).Exact)
    (hoffEpi :
      ∀ probe : TraceAnalyticAdditiveCategoryObject,
        ∀ degree : ℤ,
          (TraceAnalyticMotivicTStructure.truncLEEmbedding
            (TraceAnalyticMotivicTStructure.decompositionLowerCut 1)).r
              degree =
            none →
          Epi
            (TraceAnalyticMotivicTStructure
              .abelianEnvelopeIntrinsicCochainDecompositionProbeDegreeShortComplex
                1
                (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)
                probe
                degree).g)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
                  (hboundary represented)))) ∧
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
  let hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object)) :=
    TraceAnalyticDerivedMotiveCategory
      .current_cochainPreimage_shortExact_of_probeDegree_casewise
        object
        hlowerExact
        hlowerMono
        hoffExact
        hoffEpi
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    family_current_full_constructor_order_boundaryHandoff_literalOpcycles_certificate
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      object
      hshortExact
      represented

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
