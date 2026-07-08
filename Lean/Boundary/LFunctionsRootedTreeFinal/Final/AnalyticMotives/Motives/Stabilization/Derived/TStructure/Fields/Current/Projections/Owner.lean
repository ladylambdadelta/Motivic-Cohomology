import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.Derived.TStructure.Fields.Current.Owner

/-!
# Projections from current t-structure field fragments

This file exposes the individual proved fields from the current
t-structure-facing fragment package.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticDerivedMotiveCategory

/-- The current proved adjacent monotonicity field for the `≤` predicate. -/
theorem current_tStructureLE_zero_le :
    TraceAnalyticDerivedMotiveCategory.tStructureLE 0 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureLE 1 :=
  (TraceAnalyticDerivedMotiveCategory
    .current_tStructure_monotonicity_fields).left

/-- The current proved adjacent monotonicity field for the `≥` predicate. -/
theorem current_tStructureGE_one_le :
    TraceAnalyticDerivedMotiveCategory.tStructureGE 1 ≤
      TraceAnalyticDerivedMotiveCategory.tStructureGE 0 :=
  (TraceAnalyticDerivedMotiveCategory
    .current_tStructure_monotonicity_fields).right

end TraceAnalyticDerivedMotiveCategory

namespace TraceAnalyticMotivicTStructure

namespace RepresentedTruncationObject

/-- The current represented-object zero field agrees with the represented
composite zero theorem detected by preadditive Yoneda. -/
theorem current_represented_zero_field_eq_yoneda_detection
    (object :
      TraceAnalyticMotivicTStructure.RepresentedTruncationObject) :
    object.current_represented_zero_field =
      object.firstMap_secondMap_eq_zero_tStructure_field :=
  rfl

end RepresentedTruncationObject

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
