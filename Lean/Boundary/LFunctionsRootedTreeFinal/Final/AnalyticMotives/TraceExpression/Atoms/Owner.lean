/-!
# Trace-expression atoms

This file owns the syntactic atoms for analytic trace expressions.

The atoms defined here are not arbitrary carriers.  They are the named
analytic terms that appear in residue-channel rewriting:

* boundary trace terms;
* residue-ledger terms;
* visible channel terms;
* controlled defect and tail terms;
* weight-truncated terms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Roles of atomic analytic trace terms in the residue-channel calculus. -/
inductive TraceAtomRole where
  | boundary
  | residue
  | channel
  | defect
  | tail
  | weightTruncation
  deriving DecidableEq, Repr

/--
An indexed face of a contour presentation.

The index is syntactic.  A residue-channel presentation interprets it as an
actual boundary face in a concrete contour trace presentation.
-/
abbrev TraceFaceIndex :=
  Nat

/--
An indexed stage in a trace computation.

The index is syntactic.  A certified presentation interprets it as an actual
stage in a contour, residue, channel, refinement, or schedule computation.
-/
abbrev TraceStageIndex :=
  Nat

/--
An indexed channel in a trace computation.

The index is syntactic.  A certified presentation interprets it as a concrete
output channel, such as a geometric, spectral, boundary, defect, or tail
channel.
-/
abbrev TraceChannelIndex :=
  Nat

/-- A concrete atom in the analytic trace-expression grammar. -/
inductive TraceAtom where
  | boundary (stage : TraceStageIndex) (face : TraceFaceIndex)
  | residue (stage : TraceStageIndex) (face : TraceFaceIndex)
  | channel (stage : TraceStageIndex) (channel : TraceChannelIndex)
  | defect (stage : TraceStageIndex) (face : TraceFaceIndex)
  | tail (stage : TraceStageIndex) (channel : TraceChannelIndex)
  | weightTruncation (stage : TraceStageIndex) (level : Nat)
  deriving DecidableEq, Repr

/-- The role of a concrete trace atom. -/
def TraceAtom.role : TraceAtom → TraceAtomRole
  | boundary _ _ => TraceAtomRole.boundary
  | residue _ _ => TraceAtomRole.residue
  | channel _ _ => TraceAtomRole.channel
  | defect _ _ => TraceAtomRole.defect
  | tail _ _ => TraceAtomRole.tail
  | weightTruncation _ _ => TraceAtomRole.weightTruncation

/-- The stage index of a concrete trace atom. -/
def TraceAtom.stage : TraceAtom → TraceStageIndex
  | boundary stage _ => stage
  | residue stage _ => stage
  | channel stage _ => stage
  | defect stage _ => stage
  | tail stage _ => stage
  | weightTruncation stage _ => stage

/-- Boundary atoms have boundary role. -/
theorem TraceAtom.role_boundary
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.boundary stage face).role =
      TraceAtomRole.boundary :=
  rfl

/-- Residue atoms have residue role. -/
theorem TraceAtom.role_residue
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.residue stage face).role =
      TraceAtomRole.residue :=
  rfl

/-- Channel atoms have channel role. -/
theorem TraceAtom.role_channel
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.channel stage channel).role =
      TraceAtomRole.channel :=
  rfl

/-- Defect atoms have defect role. -/
theorem TraceAtom.role_defect
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.defect stage face).role =
      TraceAtomRole.defect :=
  rfl

/-- Tail atoms have tail role. -/
theorem TraceAtom.role_tail
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.tail stage channel).role =
      TraceAtomRole.tail :=
  rfl

/-- Weight-truncation atoms have weight-truncation role. -/
theorem TraceAtom.role_weightTruncation
    (stage : TraceStageIndex)
    (level : Nat) :
    (TraceAtom.weightTruncation stage level).role =
      TraceAtomRole.weightTruncation :=
  rfl

/-- Boundary atoms project to their stage. -/
theorem TraceAtom.stage_boundary
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.boundary stage face).stage =
      stage :=
  rfl

/-- Residue atoms project to their stage. -/
theorem TraceAtom.stage_residue
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.residue stage face).stage =
      stage :=
  rfl

/-- Channel atoms project to their stage. -/
theorem TraceAtom.stage_channel
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.channel stage channel).stage =
      stage :=
  rfl

/-- Defect atoms project to their stage. -/
theorem TraceAtom.stage_defect
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.defect stage face).stage =
      stage :=
  rfl

/-- Tail atoms project to their stage. -/
theorem TraceAtom.stage_tail
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.tail stage channel).stage =
      stage :=
  rfl

/-- Weight-truncation atoms project to their stage. -/
theorem TraceAtom.stage_weightTruncation
    (stage : TraceStageIndex)
    (level : Nat) :
    (TraceAtom.weightTruncation stage level).stage =
      stage :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
