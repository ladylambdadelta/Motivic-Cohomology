import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Compact.Owner

/-!
# Stable infinity category interface

This file owns the stable infinity category interface for compact geometric
analytic motives.  Trace realization, weight structures, `t`-structures, and
comparison with `DM_gm(ℚ)_ℚ` are downstream from this interface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The stable infinity category interface for analytic motives.  It records the
object carrier and compact analytic motives that will support the later stable
structure, weight structure, `t`-structure, trace realization, and comparison
theorems.
-/
structure AnalyticMotivicStableInfinityInterface where
  Object : Type
  compactObject : Object → Type
  compactMotive : (X : Object) → compactObject X → CompactAnalyticMotive

namespace AnalyticMotivicStableInfinityInterface

/-- The object type carried by a stable infinity category interface. -/
def objects (C : AnalyticMotivicStableInfinityInterface) : Type :=
  C.Object

/-- Compactness witnesses for objects in the interface. -/
def compactWitness (C : AnalyticMotivicStableInfinityInterface)
    (X : C.Object) : Type :=
  C.compactObject X

/-- The compact analytic motive selected by a compactness witness. -/
def compactMotiveAt (C : AnalyticMotivicStableInfinityInterface)
    (X : C.Object) (h : C.compactWitness X) :
    CompactAnalyticMotive :=
  C.compactMotive X h

/-- The stabilized presheaf of a compact object selected by a compactness witness. -/
def compactStabilizedPresheaf
    (C : AnalyticMotivicStableInfinityInterface)
    (X : C.Object) (h : C.compactWitness X) :
    TateStabilizedAnalyticPresheaf :=
  (C.compactMotiveAt X h).stabilizedPresheaf

/-- The compact-geometric closed object of a compact object selected by a witness. -/
def compactClosedObject
    (C : AnalyticMotivicStableInfinityInterface)
    (X : C.Object) (h : C.compactWitness X) :
    TateStabilizedAnalyticPresheaf :=
  (C.compactMotiveAt X h).compactClosedObject

/-- The compact-geometric closed object agrees with the stabilized presheaf. -/
theorem compactClosedObject_eq_stabilizedPresheaf
    (C : AnalyticMotivicStableInfinityInterface)
    (X : C.Object) (h : C.compactWitness X) :
    C.compactClosedObject X h =
      C.compactStabilizedPresheaf X h :=
  CompactAnalyticMotive.compactClosedObject_eq_stabilizedPresheaf
    (C.compactMotiveAt X h)

end AnalyticMotivicStableInfinityInterface

end AnalyticMotives
end LFunctions
end Boundary
