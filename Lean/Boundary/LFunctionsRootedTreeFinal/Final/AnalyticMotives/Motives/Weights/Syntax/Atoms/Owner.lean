import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.TraceExpression.Atoms.Owner

/-!
# Weight levels of trace atoms

The concrete source of analytic weights is the `weightTruncation` atom.  Other
trace atoms carry level zero at this syntactic layer.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The syntactic weight level carried by an analytic trace atom. -/
def TraceAtom.weightLevel : TraceAtom → Nat
  | TraceAtom.boundary _ _ => 0
  | TraceAtom.residue _ _ => 0
  | TraceAtom.channel _ _ => 0
  | TraceAtom.defect _ _ => 0
  | TraceAtom.tail _ _ => 0
  | TraceAtom.weightTruncation _ level => level

/-- Boundary atoms have weight level zero. -/
theorem TraceAtom.weightLevel_boundary
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.boundary stage face).weightLevel =
      0 :=
  rfl

/-- Residue atoms have weight level zero. -/
theorem TraceAtom.weightLevel_residue
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.residue stage face).weightLevel =
      0 :=
  rfl

/-- Channel atoms have weight level zero. -/
theorem TraceAtom.weightLevel_channel
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.channel stage channel).weightLevel =
      0 :=
  rfl

/-- Defect atoms have weight level zero. -/
theorem TraceAtom.weightLevel_defect
    (stage : TraceStageIndex)
    (face : TraceFaceIndex) :
    (TraceAtom.defect stage face).weightLevel =
      0 :=
  rfl

/-- Tail atoms have weight level zero. -/
theorem TraceAtom.weightLevel_tail
    (stage : TraceStageIndex)
    (channel : TraceChannelIndex) :
    (TraceAtom.tail stage channel).weightLevel =
      0 :=
  rfl

/-- A weight-truncation atom has its displayed weight level. -/
theorem TraceAtom.weightLevel_weightTruncation
    (stage : TraceStageIndex)
    (level : Nat) :
    (TraceAtom.weightTruncation stage level).weightLevel =
      level :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
