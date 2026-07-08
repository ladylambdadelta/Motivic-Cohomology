import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner
import Mathlib.Data.Complex.Basic

/-!
# Analytic trace values

This file owns the analytic interpretation target for the synthetic trace
computad.

The concrete target is a complex trace value.  Contour integrals, residues,
channels, decay terms, and Fubini interchanges imported by downstream adapters
all land in this same target.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The concrete analytic value of a trace expression. -/
abbrev AnalyticTraceValue :=
  ℂ

/-- A boundary analytic trace value. -/
def AnalyticTraceValue.boundary
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- A residue analytic trace value. -/
def AnalyticTraceValue.residue
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- A channel analytic trace value. -/
def AnalyticTraceValue.channel
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- A defect analytic trace value. -/
def AnalyticTraceValue.defect
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- A tail analytic trace value. -/
def AnalyticTraceValue.tail
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- A weight-truncation analytic trace value. -/
def AnalyticTraceValue.weightTruncation
    (value : ℂ) : AnalyticTraceValue :=
  value

/-- The channel-decomposition combination `right + horizontal - boundary`. -/
def AnalyticTraceValue.channelDecomposition
    (right horizontal boundary : AnalyticTraceValue) :
    AnalyticTraceValue :=
  right + horizontal - boundary

/-- A boundary trace value is the supplied complex value. -/
theorem AnalyticTraceValue.boundary_eq
    (value : ℂ) :
    AnalyticTraceValue.boundary value =
      value :=
  rfl

/-- A residue trace value is the supplied complex value. -/
theorem AnalyticTraceValue.residue_eq
    (value : ℂ) :
    AnalyticTraceValue.residue value =
      value :=
  rfl

/-- A channel trace value is the supplied complex value. -/
theorem AnalyticTraceValue.channel_eq
    (value : ℂ) :
    AnalyticTraceValue.channel value =
      value :=
  rfl

/-- A defect trace value is the supplied complex value. -/
theorem AnalyticTraceValue.defect_eq
    (value : ℂ) :
    AnalyticTraceValue.defect value =
      value :=
  rfl

/-- A tail trace value is the supplied complex value. -/
theorem AnalyticTraceValue.tail_eq
    (value : ℂ) :
    AnalyticTraceValue.tail value =
      value :=
  rfl

/-- A weight-truncation trace value is the supplied complex value. -/
theorem AnalyticTraceValue.weightTruncation_eq
    (value : ℂ) :
    AnalyticTraceValue.weightTruncation value =
      value :=
  rfl

/-- Channel decomposition is `right + horizontal - boundary`. -/
theorem AnalyticTraceValue.channelDecomposition_eq
    (right horizontal boundary : AnalyticTraceValue) :
    AnalyticTraceValue.channelDecomposition
        right
        horizontal
        boundary =
      right + horizontal - boundary :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
