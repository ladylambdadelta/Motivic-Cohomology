import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Projections.Owner

/-!
# Field projections from the full current t-structure fragment

This file peels the full current t-structure-facing fragment into individual
fields for downstream owner-level constructions.
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

/-- The full current fragment gives adjacent monotonicity of the analytic
aisle predicate. -/
theorem current_full_tStructureLE_zero_le
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 :=
  (represented.current_full_tStructure_monotonicity_fields
    object
    hshortExact).left

/-- The full current fragment gives adjacent monotonicity of the analytic
coaisle predicate. -/
theorem current_full_tStructureGE_one_le
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  (represented.current_full_tStructure_monotonicity_fields
    object
    hshortExact).right

/-- The full current fragment gives the arbitrary-object adjacent truncation
triangle field. -/
theorem current_full_truncation_triangle
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    ∃ (lower upper : TraceAnalyticDerivedMotiveCategory)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalLE 0 lower)
      (_ : TraceAnalyticDerivedMotiveCategory.HomologicalGE 1 upper)
      (firstMap : lower ⟶ object)
      (secondMap : object ⟶ upper)
      (connectingMap : upper ⟶ lower⟦(1 : ℤ)⟧),
      Triangle.mk firstMap secondMap connectingMap ∈
        distTriang TraceAnalyticDerivedMotiveCategory :=
  represented.current_full_exists_triangle_zero_one_field
    object
    hshortExact

/-- The full current fragment gives the represented truncation
zero-composition field. -/
theorem current_full_represented_firstMap_secondMap
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
    represented.firstMap ≫ represented.secondMap = 0 :=
  represented.current_full_represented_zero_field object hshortExact

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
