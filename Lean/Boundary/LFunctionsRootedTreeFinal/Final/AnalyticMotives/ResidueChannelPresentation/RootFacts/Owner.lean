import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Kernels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.SingularSupport.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.ResidueLedger.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Channels.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Schedules.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Certificates.AnalyticPayload.PrimitiveLengths.Owner

/-!
# Residue-channel presentation root facts

This file exposes small root facts for kernel and singular-support constructors
used by residue-channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The residue-channel root exposes boundary kernel roles. -/
theorem ResidueChannelPresentation.kernel_boundary_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).role =
      TraceKernelRole.boundary :=
  TraceKernelAtom.boundary_role
    stage
    face
    expression

/-- The residue-channel root exposes channel kernel expressions. -/
theorem ResidueChannelPresentation.kernel_channel_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).expression =
      expression :=
  TraceKernelAtom.channel_expression
    stage
    channel
    expression

/-- The residue-channel root exposes pole singular-support roles. -/
theorem ResidueChannelPresentation.singularSupport_pole_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).role =
      TraceSingularSupportRole.pole :=
  TraceSingularSupportAtom.pole_role
    stage
    face

/-- The residue-channel root exposes deformation-barrier support stages. -/
theorem ResidueChannelPresentation.singularSupport_deformationBarrier_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).stage =
      stage :=
  TraceSingularSupportAtom.deformationBarrier_stage
    stage
    channel

end AnalyticMotives
end LFunctions
end Boundary
