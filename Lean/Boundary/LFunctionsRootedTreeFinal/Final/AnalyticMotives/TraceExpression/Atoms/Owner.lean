/-!
# Trace-expression atoms

This file owns the syntactic atoms for analytic trace expressions.

The intended atoms are not arbitrary carriers.  They are the named analytic
terms that appear in residue-channel rewriting:

* boundary trace terms;
* residue-ledger terms;
* visible channel terms;
* controlled defect and tail terms;
* weight-truncated terms.

The next implementation step is to define these atoms as a concrete grammar for
analytic trace expressions, before any category or motive construction.
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

end AnalyticMotives
end LFunctions
end Boundary
