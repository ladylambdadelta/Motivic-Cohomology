import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Full.Owner

/-!
# Projections from the full current t-structure field fragment

This file exposes the individual fields assembled by the full current
t-structure-facing fragment.
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

/-- The adjacent monotonicity fields extracted from the full current
t-structure-facing fragment. -/
theorem current_full_tStructure_monotonicity_fields
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
        TraceAnalyticDerivedMotiveCategory.tStructureLE 1 ∧
      TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
        TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  (represented.current_full_tStructure_fragment object hshortExact).left

/-- The arbitrary-object adjacent truncation-existence field extracted from
the full current t-structure-facing fragment. -/
theorem current_full_exists_triangle_zero_one_field
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
  (represented.current_full_tStructure_fragment object hshortExact).right.left

/-- The represented-object zero-composition field extracted from the full
current t-structure-facing fragment. -/
theorem current_full_represented_zero_field
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
  (represented.current_full_tStructure_fragment object hshortExact).right.right

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
