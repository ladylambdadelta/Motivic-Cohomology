import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Constructors.Owner

/-!
# Full current t-structure field fragment

This file combines the currently proved derived analytic t-structure-facing
fields: adjacent monotonicity, arbitrary-object truncation existence through
the canonical cochain preimage, and represented-object zero-composition in
the `zero'`-field shape.
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

/-- The full currently proved t-structure-facing package: adjacent
monotonicity, arbitrary-object truncation existence through the canonical
cochain preimage, and represented-object zero-composition. -/
theorem current_full_tStructure_fragment
    (represented :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject)
    (object : TraceAnalyticDerivedMotiveCategory)
    (hshortExact :
      TraceAnalyticAbelianCochainComplex.shortExact
        (TraceAnalyticMotivicTStructure
          .abelianEnvelopeIntrinsicCochainDecompositionShortComplex
            1
            (TraceAnalyticDerivedMotiveCategory.cochainPreimage object))) :
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
        .current_exists_triangle_zero_one_field_of_shortExact
          object
          hshortExact)
      represented.current_represented_zero_field)

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
