import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Analytic.TraceValue.Owner

/-!
# Top-root analytic trace values

This file exposes the concrete complex-valued analytic trace-value target at
the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A boundary analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_boundary_eq
    (value : ℂ) :
    AnalyticTraceValue.boundary value =
      value :=
  AnalyticTraceValue.boundary_eq
    value

/-- A residue analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_residue_eq
    (value : ℂ) :
    AnalyticTraceValue.residue value =
      value :=
  AnalyticTraceValue.residue_eq
    value

/-- A channel analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_channel_eq
    (value : ℂ) :
    AnalyticTraceValue.channel value =
      value :=
  AnalyticTraceValue.channel_eq
    value

/-- A defect analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_defect_eq
    (value : ℂ) :
    AnalyticTraceValue.defect value =
      value :=
  AnalyticTraceValue.defect_eq
    value

/-- A tail analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_tail_eq
    (value : ℂ) :
    AnalyticTraceValue.tail value =
      value :=
  AnalyticTraceValue.tail_eq
    value

/-- A weight-truncation analytic trace value is the supplied complex value. -/
theorem AnalyticMotivesRoot.analyticTraceValue_weightTruncation_eq
    (value : ℂ) :
    AnalyticTraceValue.weightTruncation value =
      value :=
  AnalyticTraceValue.weightTruncation_eq
    value

/-- Channel decomposition is `right + horizontal - boundary`. -/
theorem AnalyticMotivesRoot.analyticTraceValue_channelDecomposition_eq
    (right horizontal boundary : AnalyticTraceValue) :
    AnalyticTraceValue.channelDecomposition
        right
        horizontal
        boundary =
      right + horizontal - boundary :=
  AnalyticTraceValue.channelDecomposition_eq
    right
    horizontal
    boundary

end AnalyticMotives
end LFunctions
end Boundary
