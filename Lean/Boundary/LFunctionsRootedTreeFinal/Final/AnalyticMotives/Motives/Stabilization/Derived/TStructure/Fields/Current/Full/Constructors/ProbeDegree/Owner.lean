import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Owner

/-!
# Probe-degree constructor for the full current field fragment

This file assembles the full current t-structure-facing fragment directly from
probe-degree lower-tail and off-tail data on the canonical cochain preimage.
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

/-- Probe-degree lower-tail and off-tail analytic exactness data on the
canonical cochain preimage give the full current t-structure-facing package:
adjacent monotonicity, adjacent truncation existence, and represented-object
zero-composition. -/
theorem current_full_tStructure_fragment_of_probeDegree_casewise
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
    (TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureGE 0) ∧
      (∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
        (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
        (firstMap : lower ⟶ object)
        (secondMap : object ⟶ upper)
        (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
        Triangle.mk firstMap secondMap connectingMap ∈
          distTriang TraceAnalyticDerivedMotiveCategory) ∧
        represented.firstMap ≫ represented.secondMap = 0 :=
  And.intro
    TraceAnalyticDerivedMotiveCategory.current_tStructure_monotonicity_fields
    (And.intro
      (TraceAnalyticDerivedMotiveCategory
        .current_exists_triangle_zero_one_field_of_probeDegree_casewise
          object
          hlowerExact
          hlowerMono
          hoffExact
          hoffEpi)
      represented.current_represented_zero_field)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
