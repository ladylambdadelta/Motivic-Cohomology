import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Realizations.Algebraic.TraceValue.Owner

/-!
# Top-root algebraic trace values

This file exposes the concrete trace-correspondence hom target for algebraic
trace values at the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Algebraic trace-value modules are representable sections. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_module_eq_representable_sections
    (source target : TraceCorQObject) :
    AlgebraicTraceValue.module source target =
      (TraceCorQPresheaf.representable target).sections source :=
  AlgebraicTraceValue.module_eq_representable_sections
    source
    target

/-- A boundary algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_boundary_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.boundary value =
      value :=
  AlgebraicTraceValue.boundary_eq
    value

/-- A residue algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_residue_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.residue value =
      value :=
  AlgebraicTraceValue.residue_eq
    value

/-- A channel algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_channel_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.channel value =
      value :=
  AlgebraicTraceValue.channel_eq
    value

/-- A defect algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_defect_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.defect value =
      value :=
  AlgebraicTraceValue.defect_eq
    value

/-- A tail algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_tail_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.tail value =
      value :=
  AlgebraicTraceValue.tail_eq
    value

/-- A weight-truncation algebraic trace value is the supplied trace correspondence. -/
theorem AnalyticMotivesRoot.algebraicTraceValue_weightTruncation_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.weightTruncation value =
      value :=
  AlgebraicTraceValue.weightTruncation_eq
    value

end AnalyticMotives
end LFunctions
end Boundary
