import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Certificate.FieldOrder.Constructors.ProbeDegree.BoundaryHandoff.Family.Global.Projections.Owner

/-!
# Field projections from global probe-degree family boundary handoff

This file exposes the individual constructor-order t-structure fields carried
by the global probe-degree family boundary handoff package.
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

/-- Global probe-degree family boundary handoff gives adjacent monotonicity of
the analytic aisle predicate. -/
theorem family_globalProbeDegree_boundaryHandoff_tStructureLE_zero_le
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
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (family_globalProbeDegree_boundaryHandoff_fields
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object
      represented).left

/-- Global probe-degree family boundary handoff gives adjacent monotonicity of
the analytic coaisle predicate. -/
theorem family_globalProbeDegree_boundaryHandoff_tStructureGE_one_le
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
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (family_globalProbeDegree_boundaryHandoff_fields
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object
      represented).right.left

/-- Global probe-degree family boundary handoff gives adjacent truncation
triangle existence. -/
theorem family_globalProbeDegree_boundaryHandoff_truncation_triangle
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
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
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
    (family_globalProbeDegree_boundaryHandoff_fields
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object
      represented).right.right.left

/-- Global probe-degree family boundary handoff gives represented-object
zero-composition. -/
theorem family_globalProbeDegree_boundaryHandoff_represented_firstMap_secondMap
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
    (hlowerExact :
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
      ∀ object : TraceAnalyticDerivedMotiveCategory,
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
    (object : TraceAnalyticDerivedMotiveCategory)
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    letI : ∀ degree : ℤ,
        represented.representative.complex.HasHomology degree :=
      represented.representative.hasHomology
    represented.firstMap ≫ represented.secondMap = 0 := by
  letI : ∀ degree : ℤ,
      represented.representative.complex.HasHomology degree :=
    represented.representative.hasHomology
  exact
    (family_globalProbeDegree_boundaryHandoff_fields
      opcyclesSplit
      tail
      htail
      hboundary
      hrange
      hlowerExact
      hlowerMono
      hoffExact
      hoffEpi
      object
      represented).right.right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
