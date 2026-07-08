import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.ResidueChannelPresentation.Stage.Owner

/-!
# Singular supports

This file owns finite singular-support bookkeeping for trace presentations.

The entries are syntactic locations in the trace calculus: poles, cuts,
excluded loci, and deformation barriers.  Concrete non-crossing and residue
claims are certified later by analytic certificate atoms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The role of a singular-support entry in a trace presentation. -/
inductive TraceSingularSupportRole where
  | pole
  | cut
  | excludedLocus
  | deformationBarrier
  deriving DecidableEq, Repr

/-- A finite syntactic singular-support atom. -/
inductive TraceSingularSupportAtom where
  | pole (stage : ResidueChannelStage) (face : TraceFaceIndex)
  | cut (stage : ResidueChannelStage) (face : TraceFaceIndex)
  | excludedLocus (stage : ResidueChannelStage) (channel : TraceChannelIndex)
  | deformationBarrier (stage : ResidueChannelStage) (channel : TraceChannelIndex)
  deriving DecidableEq, Repr

/-- The role of a singular-support atom. -/
def TraceSingularSupportAtom.role :
    TraceSingularSupportAtom → TraceSingularSupportRole
  | pole _ _ => TraceSingularSupportRole.pole
  | cut _ _ => TraceSingularSupportRole.cut
  | excludedLocus _ _ => TraceSingularSupportRole.excludedLocus
  | deformationBarrier _ _ => TraceSingularSupportRole.deformationBarrier

/-- The stage of a singular-support atom. -/
def TraceSingularSupportAtom.stage :
    TraceSingularSupportAtom → ResidueChannelStage
  | pole stage _ => stage
  | cut stage _ => stage
  | excludedLocus stage _ => stage
  | deformationBarrier stage _ => stage

/-- A pole support atom has pole role. -/
theorem TraceSingularSupportAtom.pole_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).role =
      TraceSingularSupportRole.pole :=
  rfl

/-- A cut support atom has cut role. -/
theorem TraceSingularSupportAtom.cut_role
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.cut stage face).role =
      TraceSingularSupportRole.cut :=
  rfl

/-- An excluded-locus support atom has excluded-locus role. -/
theorem TraceSingularSupportAtom.excludedLocus_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.excludedLocus stage channel).role =
      TraceSingularSupportRole.excludedLocus :=
  rfl

/-- A deformation-barrier support atom has deformation-barrier role. -/
theorem TraceSingularSupportAtom.deformationBarrier_role
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).role =
      TraceSingularSupportRole.deformationBarrier :=
  rfl

/-- A pole support atom has the supplied stage. -/
theorem TraceSingularSupportAtom.pole_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.pole stage face).stage =
      stage :=
  rfl

/-- A cut support atom has the supplied stage. -/
theorem TraceSingularSupportAtom.cut_stage
    (stage : ResidueChannelStage) (face : TraceFaceIndex) :
    (TraceSingularSupportAtom.cut stage face).stage =
      stage :=
  rfl

/-- An excluded-locus support atom has the supplied stage. -/
theorem TraceSingularSupportAtom.excludedLocus_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.excludedLocus stage channel).stage =
      stage :=
  rfl

/-- A deformation-barrier support atom has the supplied stage. -/
theorem TraceSingularSupportAtom.deformationBarrier_stage
    (stage : ResidueChannelStage) (channel : TraceChannelIndex) :
    (TraceSingularSupportAtom.deformationBarrier stage channel).stage =
      stage :=
  rfl

/-- A finite singular-support list. -/
abbrev TraceSingularSupport :=
  List TraceSingularSupportAtom

/-- The empty singular-support list. -/
def TraceSingularSupport.empty : TraceSingularSupport :=
  []

/-- Add one singular-support atom to a finite support list. -/
def TraceSingularSupport.cons
    (atom : TraceSingularSupportAtom)
    (support : TraceSingularSupport) :
    TraceSingularSupport :=
  atom :: support

/-- The empty singular support is the empty list. -/
theorem TraceSingularSupport.empty_eq_nil :
    TraceSingularSupport.empty = [] :=
  rfl

/-- Singular-support cons is list cons. -/
theorem TraceSingularSupport.cons_eq_cons
    (atom : TraceSingularSupportAtom)
    (support : TraceSingularSupport) :
    TraceSingularSupport.cons atom support =
      atom :: support :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
