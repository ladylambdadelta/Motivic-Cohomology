import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Presheaves.Representables.Owner

/-!
# Algebraic trace values

This file owns the algebraic interpretation target for the synthetic trace
computad.

At this stage the algebraic target is the trace-correspondence hom itself,
viewed through the Q-linear representable presheaf calculus.  This is the
concrete algebraic-facing value supplied by the proved `TraceCorQ` category;
comparison with finite correspondences is stated downstream over this target.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete algebraic value of a trace from `source` to `target`. -/
abbrev AlgebraicTraceValue
    (source target : TraceCorQObject) :=
  source ⟶ target

/-- The representable Q-module containing algebraic trace values from `source` to `target`. -/
def AlgebraicTraceValue.module
    (source target : TraceCorQObject) :
    ModuleCat Rat :=
  ModuleCat.of Rat (AlgebraicTraceValue source target)

/-- A boundary algebraic trace value. -/
def AlgebraicTraceValue.boundary
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- A residue algebraic trace value. -/
def AlgebraicTraceValue.residue
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- A channel algebraic trace value. -/
def AlgebraicTraceValue.channel
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- A defect algebraic trace value. -/
def AlgebraicTraceValue.defect
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- A tail algebraic trace value. -/
def AlgebraicTraceValue.tail
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- A weight-truncation algebraic trace value. -/
def AlgebraicTraceValue.weightTruncation
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue source target :=
  value

/-- Algebraic trace-value modules are the sections of the target representable at the source. -/
theorem AlgebraicTraceValue.module_eq_representable_sections
    (source target : TraceCorQObject) :
    AlgebraicTraceValue.module source target =
      (TraceCorQPresheaf.representable target).sections source :=
  Eq.symm
    (TraceCorQPresheaf.representable_sections
      source
      target)

/-- A boundary algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.boundary_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.boundary value =
      value :=
  rfl

/-- A residue algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.residue_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.residue value =
      value :=
  rfl

/-- A channel algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.channel_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.channel value =
      value :=
  rfl

/-- A defect algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.defect_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.defect value =
      value :=
  rfl

/-- A tail algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.tail_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.tail value =
      value :=
  rfl

/-- A weight-truncation algebraic trace value is the supplied trace correspondence. -/
theorem AlgebraicTraceValue.weightTruncation_eq
    {source target : TraceCorQObject}
    (value : AlgebraicTraceValue source target) :
    AlgebraicTraceValue.weightTruncation value =
      value :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
