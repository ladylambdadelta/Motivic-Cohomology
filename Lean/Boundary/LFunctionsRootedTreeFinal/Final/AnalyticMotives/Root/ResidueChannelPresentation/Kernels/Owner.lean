import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Kernels.Owner

/-!
# Top-root residue-channel kernels

This file exposes finite syntactic analytic-kernel bookkeeping.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes roles of boundary kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_boundary_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).role =
      TraceKernelRole.boundary :=
  TraceKernelAtom.boundary_role stage face expression

/-- The top root exposes roles of residue kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_residue_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).role =
      TraceKernelRole.residue :=
  TraceKernelAtom.residue_role stage face expression

/-- The top root exposes roles of channel kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_channel_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).role =
      TraceKernelRole.channel :=
  TraceKernelAtom.channel_role stage channel expression

/-- The top root exposes roles of defect kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_defect_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).role =
      TraceKernelRole.defect :=
  TraceKernelAtom.defect_role stage face expression

/-- The top root exposes roles of tail kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_tail_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).role =
      TraceKernelRole.tail :=
  TraceKernelAtom.tail_role stage channel expression

/-- The top root exposes roles of weight-truncation kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_weightTruncation_role
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).role =
      TraceKernelRole.weightTruncation :=
  TraceKernelAtom.weightTruncation_role stage level expression

/-- The top root exposes stages of boundary kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_boundary_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).stage =
      stage :=
  TraceKernelAtom.boundary_stage stage face expression

/-- The top root exposes stages of residue kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_residue_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).stage =
      stage :=
  TraceKernelAtom.residue_stage stage face expression

/-- The top root exposes stages of channel kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_channel_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).stage =
      stage :=
  TraceKernelAtom.channel_stage stage channel expression

/-- The top root exposes stages of defect kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_defect_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).stage =
      stage :=
  TraceKernelAtom.defect_stage stage face expression

/-- The top root exposes stages of tail kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_tail_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).stage =
      stage :=
  TraceKernelAtom.tail_stage stage channel expression

/-- The top root exposes stages of weight-truncation kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_weightTruncation_stage
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).stage =
      stage :=
  TraceKernelAtom.weightTruncation_stage stage level expression

/-- The top root exposes expressions of boundary kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_boundary_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).expression =
      expression :=
  TraceKernelAtom.boundary_expression stage face expression

/-- The top root exposes expressions of residue kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_residue_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.residue stage face expression).expression =
      expression :=
  TraceKernelAtom.residue_expression stage face expression

/-- The top root exposes expressions of channel kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_channel_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).expression =
      expression :=
  TraceKernelAtom.channel_expression stage channel expression

/-- The top root exposes expressions of defect kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_defect_expression
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.defect stage face expression).expression =
      expression :=
  TraceKernelAtom.defect_expression stage face expression

/-- The top root exposes expressions of tail kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_tail_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.tail stage channel expression).expression =
      expression :=
  TraceKernelAtom.tail_expression stage channel expression

/-- The top root exposes expressions of weight-truncation kernel atoms. -/
theorem AnalyticMotivesRoot.traceKernelAtom_weightTruncation_expression
    (stage : ResidueChannelStage) (level : Nat)
    (expression : QTraceExpression) :
    (TraceKernelAtom.weightTruncation stage level expression).expression =
      expression :=
  TraceKernelAtom.weightTruncation_expression stage level expression

/-- The top root exposes the empty analytic-kernel list. -/
def AnalyticMotivesRoot.traceKernelList_empty : TraceKernelList :=
  TraceKernelList.empty

/-- The top root exposes analytic-kernel list cons. -/
def AnalyticMotivesRoot.traceKernelList_cons
    (atom : TraceKernelAtom) (kernels : TraceKernelList) :
    TraceKernelList :=
  TraceKernelList.cons atom kernels

/-- The top root exposes the empty analytic-kernel list as the empty list. -/
theorem AnalyticMotivesRoot.traceKernelList_empty_eq_nil :
    TraceKernelList.empty = [] :=
  TraceKernelList.empty_eq_nil

/-- The top root exposes analytic-kernel cons as list cons. -/
theorem AnalyticMotivesRoot.traceKernelList_cons_eq_cons
    (atom : TraceKernelAtom) (kernels : TraceKernelList) :
    TraceKernelList.cons atom kernels =
      atom :: kernels :=
  TraceKernelList.cons_eq_cons atom kernels

end AnalyticMotives
end LFunctions
end Boundary
