import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.QLinear.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Analytic kernels

This file owns finite syntactic kernel bookkeeping for residue-channel
presentations.

The kernel layer records which Q-linear trace expression is being interpreted
as a boundary, residue, channel, defect, tail, or weight-truncation kernel at a
given stage.  Concrete analytic validation enters later through certificates.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The role played by a kernel entry in a residue-channel presentation. -/
inductive TraceKernelRole where
  | boundary
  | residue
  | channel
  | defect
  | tail
  | weightTruncation
  deriving DecidableEq, Repr

/-- A finite syntactic analytic-kernel entry. -/
inductive TraceKernelAtom where
  | boundary (stage : ResidueChannelStage) (face : TraceFaceIndex)
      (expression : QTraceExpression)
  | residue (stage : ResidueChannelStage) (face : TraceFaceIndex)
      (expression : QTraceExpression)
  | channel (stage : ResidueChannelStage) (channel : TraceChannelIndex)
      (expression : QTraceExpression)
  | defect (stage : ResidueChannelStage) (face : TraceFaceIndex)
      (expression : QTraceExpression)
  | tail (stage : ResidueChannelStage) (channel : TraceChannelIndex)
      (expression : QTraceExpression)
  | weightTruncation (stage : ResidueChannelStage) (level : Nat)
      (expression : QTraceExpression)
  deriving Repr

/-- The role of a kernel atom. -/
def TraceKernelAtom.role : TraceKernelAtom → TraceKernelRole
  | boundary _ _ _ => TraceKernelRole.boundary
  | residue _ _ _ => TraceKernelRole.residue
  | channel _ _ _ => TraceKernelRole.channel
  | defect _ _ _ => TraceKernelRole.defect
  | tail _ _ _ => TraceKernelRole.tail
  | weightTruncation _ _ _ => TraceKernelRole.weightTruncation

/-- The stage of a kernel atom. -/
def TraceKernelAtom.stage : TraceKernelAtom → ResidueChannelStage
  | boundary stage _ _ => stage
  | residue stage _ _ => stage
  | channel stage _ _ => stage
  | defect stage _ _ => stage
  | tail stage _ _ => stage
  | weightTruncation stage _ _ => stage

/-- The Q-linear trace expression carried by a kernel atom. -/
def TraceKernelAtom.expression : TraceKernelAtom → QTraceExpression
  | boundary _ _ expression => expression
  | residue _ _ expression => expression
  | channel _ _ expression => expression
  | defect _ _ expression => expression
  | tail _ _ expression => expression
  | weightTruncation _ _ expression => expression

/-- A boundary kernel atom has boundary role. -/
theorem TraceKernelAtom.boundary_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).role =
      TraceKernelRole.boundary :=
  rfl

/-- A residue kernel atom has residue role. -/
theorem TraceKernelAtom.residue_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).role =
      TraceKernelRole.residue :=
  rfl

/-- A channel kernel atom has channel role. -/
theorem TraceKernelAtom.channel_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).role =
      TraceKernelRole.channel :=
  rfl

/-- A defect kernel atom has defect role. -/
theorem TraceKernelAtom.defect_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).role =
      TraceKernelRole.defect :=
  rfl

/-- A tail kernel atom has tail role. -/
theorem TraceKernelAtom.tail_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).role =
      TraceKernelRole.tail :=
  rfl

/-- A weight-truncation kernel atom has weight-truncation role. -/
theorem TraceKernelAtom.weightTruncation_role
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).role =
      TraceKernelRole.weightTruncation :=
  rfl

/-- A boundary kernel atom has the supplied stage. -/
theorem TraceKernelAtom.boundary_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).stage =
      stage :=
  rfl

/-- A residue kernel atom has the supplied stage. -/
theorem TraceKernelAtom.residue_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).stage =
      stage :=
  rfl

/-- A channel kernel atom has the supplied stage. -/
theorem TraceKernelAtom.channel_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).stage =
      stage :=
  rfl

/-- A defect kernel atom has the supplied stage. -/
theorem TraceKernelAtom.defect_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).stage =
      stage :=
  rfl

/-- A tail kernel atom has the supplied stage. -/
theorem TraceKernelAtom.tail_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).stage =
      stage :=
  rfl

/-- A weight-truncation kernel atom has the supplied stage. -/
theorem TraceKernelAtom.weightTruncation_stage
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).stage =
      stage :=
  rfl

/-- A boundary kernel atom has the supplied expression. -/
theorem TraceKernelAtom.boundary_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).expression =
      expression :=
  rfl

/-- A residue kernel atom has the supplied expression. -/
theorem TraceKernelAtom.residue_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).expression =
      expression :=
  rfl

/-- A channel kernel atom has the supplied expression. -/
theorem TraceKernelAtom.channel_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).expression =
      expression :=
  rfl

/-- A defect kernel atom has the supplied expression. -/
theorem TraceKernelAtom.defect_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).expression =
      expression :=
  rfl

/-- A tail kernel atom has the supplied expression. -/
theorem TraceKernelAtom.tail_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).expression =
      expression :=
  rfl

/-- A weight-truncation kernel atom has the supplied expression. -/
theorem TraceKernelAtom.weightTruncation_expression
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).expression =
      expression :=
  rfl

/-- A finite analytic-kernel list. -/
abbrev TraceKernelList :=
  List TraceKernelAtom

/-- The empty analytic-kernel list. -/
def TraceKernelList.empty : TraceKernelList :=
  []

/-- Add one analytic-kernel atom to a finite kernel list. -/
def TraceKernelList.cons
    (atom : TraceKernelAtom) (kernels : TraceKernelList) :
    TraceKernelList :=
  atom :: kernels

/-- The empty analytic-kernel list is the empty list. -/
theorem TraceKernelList.empty_eq_nil :
    TraceKernelList.empty = [] :=
  rfl

/-- Kernel-list cons is list cons. -/
theorem TraceKernelList.cons_eq_cons
    (atom : TraceKernelAtom) (kernels : TraceKernelList) :
    TraceKernelList.cons atom kernels =
      atom :: kernels :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
