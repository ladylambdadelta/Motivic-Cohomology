import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Owner

/-!
# Top-root residue-channel presentation core facts

This file exposes the basic kernel and singular-support facts used by certified
residue-channel presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes boundary kernel roles. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_kernel_boundary_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.boundary stage face expression).role =
      TraceKernelRole.boundary :=
  ResidueChannelPresentation.kernel_boundary_role
    stage
    face
    expression

/-- The top root exposes channel kernel expressions. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_kernel_channel_expression
    (stage : ResidueChannelStage) (channel : TraceChannelIndex)
    (expression : QTraceExpression) :
    (TraceKernelAtom.channel stage channel expression).expression =
      expression :=
  ResidueChannelPresentation.kernel_channel_expression
    stage
    channel
    expression

/-- The top root exposes pole singular-support roles. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_singularSupport_pole_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).role =
      TraceSingularSupportRole.pole :=
  ResidueChannelPresentation.singularSupport_pole_role
    stage
    face

/-- The top root exposes deformation-barrier singular-support stages. -/
theorem AnalyticMotivesRoot.residueChannelPresentation_singularSupport_deformationBarrier_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).stage =
      stage :=
  ResidueChannelPresentation.singularSupport_deformationBarrier_stage
    stage
    channel

end AnalyticMotives
end LFunctions
end Boundary
