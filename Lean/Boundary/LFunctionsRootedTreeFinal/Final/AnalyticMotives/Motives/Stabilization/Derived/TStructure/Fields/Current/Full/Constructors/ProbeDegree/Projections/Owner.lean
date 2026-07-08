import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Constructors.ProbeDegree.Owner

/-!
# Projections from the probe-degree full current fragment

This file exposes the grouped fields obtained from the probe-degree full
current t-structure-facing fragment.
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

/-- The probe-degree full fragment gives both adjacent monotonicity fields. -/
theorem current_full_fragment_probeDegree_monotonicity_fields
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
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
                degree).g) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  (represented.current_full_tStructure_fragment_of_probeDegree_casewise
    object
    hlowerExact
    hlowerMono
    hoffExact
    hoffEpi).left

/-- The probe-degree full fragment gives adjacent truncation triangle
existence. -/
theorem current_full_fragment_probeDegree_truncation_triangle
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
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
                degree).g) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  (represented.current_full_tStructure_fragment_of_probeDegree_casewise
    object
    hlowerExact
    hlowerMono
    hoffExact
    hoffEpi).right.left

/-- The probe-degree full fragment gives represented-object zero-composition. -/
theorem current_full_fragment_probeDegree_represented_zero_field
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
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
                degree).g) :
    represented.firstMap ≫ represented.secondMap = 0 :=
  (represented.current_full_tStructure_fragment_of_probeDegree_casewise
    object
    hlowerExact
    hlowerMono
    hoffExact
    hoffEpi).right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
