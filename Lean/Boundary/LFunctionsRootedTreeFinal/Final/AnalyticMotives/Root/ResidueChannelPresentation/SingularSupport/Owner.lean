import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.SingularSupport.Owner

/-!
# Top-root residue-channel singular support

This file exposes finite singular-support bookkeeping for trace presentations.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The top root exposes pole singular-support roles. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_pole_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).role =
      TraceSingularSupportRole.pole :=
  TraceSingularSupportAtom.pole_role stage face

/-- The top root exposes cut singular-support roles. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_cut_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.cut stage face).role =
      TraceSingularSupportRole.cut :=
  TraceSingularSupportAtom.cut_role stage face

/-- The top root exposes excluded-locus singular-support roles. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_excludedLocus_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.excludedLocus stage channel).role =
      TraceSingularSupportRole.excludedLocus :=
  TraceSingularSupportAtom.excludedLocus_role stage channel

/-- The top root exposes deformation-barrier singular-support roles. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_deformationBarrier_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).role =
      TraceSingularSupportRole.deformationBarrier :=
  TraceSingularSupportAtom.deformationBarrier_role stage channel

/-- The top root exposes pole singular-support stages. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_pole_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).stage =
      stage :=
  TraceSingularSupportAtom.pole_stage stage face

/-- The top root exposes cut singular-support stages. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_cut_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.cut stage face).stage =
      stage :=
  TraceSingularSupportAtom.cut_stage stage face

/-- The top root exposes excluded-locus singular-support stages. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_excludedLocus_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.excludedLocus stage channel).stage =
      stage :=
  TraceSingularSupportAtom.excludedLocus_stage stage channel

/-- The top root exposes deformation-barrier singular-support stages. -/
theorem AnalyticMotivesRoot.traceSingularSupportAtom_deformationBarrier_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).stage =
      stage :=
  TraceSingularSupportAtom.deformationBarrier_stage stage channel

/-- The top root exposes the empty singular-support list. -/
def AnalyticMotivesRoot.traceSingularSupport_empty : TraceSingularSupport :=
  TraceSingularSupport.empty

/-- The top root exposes singular-support list cons. -/
def AnalyticMotivesRoot.traceSingularSupport_cons
    (atom : TraceSingularSupportAtom)
    (support : TraceSingularSupport) :
    TraceSingularSupport :=
  TraceSingularSupport.cons atom support

/-- The top root exposes the empty singular support as the empty list. -/
theorem AnalyticMotivesRoot.traceSingularSupport_empty_eq_nil :
    TraceSingularSupport.empty = [] :=
  TraceSingularSupport.empty_eq_nil

/-- The top root exposes singular-support cons as list cons. -/
theorem AnalyticMotivesRoot.traceSingularSupport_cons_eq_cons
    (atom : TraceSingularSupportAtom)
    (support : TraceSingularSupport) :
    TraceSingularSupport.cons atom support =
      atom :: support :=
  TraceSingularSupport.cons_eq_cons atom support

end AnalyticMotives
end LFunctions
end Boundary
