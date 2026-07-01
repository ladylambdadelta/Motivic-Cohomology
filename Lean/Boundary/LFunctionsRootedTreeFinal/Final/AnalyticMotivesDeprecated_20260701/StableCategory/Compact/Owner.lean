import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Stabilized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.Owner

/-!
# Compact geometric analytic motive category

This file owns the compact geometric analytic motive category after Tate
stabilization and idempotent completion.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The compact geometric analytic motive layer after Tate stabilization and
idempotent completion.
-/
structure CompactAnalyticMotive where
  stabilized : StabilizedAnalyticMotive
  compactGeometric : CompactGeometricAnalyticMotive
  compactGeometric_closedObject_eq :
    compactGeometric.thickClosure.closedObject =
      stabilized.stabilizedPresheaf

namespace CompactAnalyticMotive

/-- The stabilized analytic motive underlying a compact analytic motive. -/
def stabilizedPart (M : CompactAnalyticMotive) :
    StabilizedAnalyticMotive :=
  M.stabilized

/-- The compact geometric component of a compact analytic motive. -/
def compactPart (M : CompactAnalyticMotive) :
    CompactGeometricAnalyticMotive :=
  M.compactGeometric

/-- The Tate-stabilized presheaf carried by the stabilized component. -/
def stabilizedPresheaf (M : CompactAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.stabilized.stabilizedPresheaf

/-- The compact-geometric closed object of a compact analytic motive. -/
def compactClosedObject (M : CompactAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.compactGeometric.closedObject

/-- The compact-geometric retract object of a compact analytic motive. -/
def compactRetractObject (M : CompactAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.compactGeometric.retractObject

/-- The compact-geometric closed object agrees with the stabilized presheaf. -/
theorem compactClosedObject_eq_stabilizedPresheaf
    (M : CompactAnalyticMotive) :
    M.compactClosedObject = M.stabilizedPresheaf :=
  M.compactGeometric_closedObject_eq

end CompactAnalyticMotive

/--
The compact geometric analytic motive layer carrying functorial rational
transfer laws through stabilization and compact-geometric completion.
-/
structure FunctorialCompactAnalyticMotive where
  stabilized : FunctorialStabilizedAnalyticMotive
  compactGeometric : FunctorialCompactGeometricAnalyticMotive
  compactGeometric_closedObject_eq :
    compactGeometric.functorialThickClosure.closedObject =
      stabilized.stabilizedPresheaf

namespace FunctorialCompactAnalyticMotive

/-- Forget functorial transfer laws from a compact analytic motive. -/
def forget (M : FunctorialCompactAnalyticMotive) :
    CompactAnalyticMotive where
  stabilized := M.stabilized.forget
  compactGeometric := M.compactGeometric.forget
  compactGeometric_closedObject_eq :=
    congrArg FunctorialTateStabilizedAnalyticPresheaf.forget
      M.compactGeometric_closedObject_eq

/-- The functorial stabilized analytic motive underlying a compact motive. -/
def stabilizedPart (M : FunctorialCompactAnalyticMotive) :
    FunctorialStabilizedAnalyticMotive :=
  M.stabilized

/-- The functorial compact-geometric component. -/
def compactPart (M : FunctorialCompactAnalyticMotive) :
    FunctorialCompactGeometricAnalyticMotive :=
  M.compactGeometric

/-- The functorial Tate-stabilized presheaf carried by the stabilized component. -/
def stabilizedPresheaf (M : FunctorialCompactAnalyticMotive) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  M.stabilized.stabilizedPresheaf

/-- The functorial compact-geometric closed object. -/
def compactClosedObject (M : FunctorialCompactAnalyticMotive) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  M.compactGeometric.closedObject

/-- The compact-geometric retract object. -/
def compactRetractObject (M : FunctorialCompactAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.compactGeometric.retractObject

/--
The compact-geometric closed object agrees with the stabilized object in a
functorial compact analytic motive.
-/
theorem compactGeometric_closedObject_compatibility
    (M : FunctorialCompactAnalyticMotive) :
    M.compactGeometric.functorialThickClosure.closedObject =
      M.stabilized.stabilizedPresheaf :=
  M.compactGeometric_closedObject_eq

/-- The transfer action retained by the stabilized component. -/
def stabilizedTransferAction (M : FunctorialCompactAnalyticMotive) :
    RationalContourTransferAction
      (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialStabilizedAnalyticMotive.transferAction M.stabilized

/-- The transfer action retained by the compact-geometric component. -/
def compactTransferAction (M : FunctorialCompactAnalyticMotive) :
    RationalContourTransferAction
      (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialCompactGeometricAnalyticMotive.transferAction
    M.compactGeometric

/--
Reindexing invariance for pullbacks carried by the stabilized component of a
functorial compact analytic motive.
-/
theorem stabilized_reindexing_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (stabilizedTransferAction M).act f =
      (stabilizedTransferAction M).act g :=
  FunctorialStabilizedAnalyticMotive.reindexing_pullback_eq
    M.stabilized f g R

/--
Reindexing invariance for pullbacks carried by the compact-geometric component
of a functorial compact analytic motive.
-/
theorem compact_reindexing_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (compactTransferAction M).act f =
      (compactTransferAction M).act g :=
  FunctorialCompactGeometricAnalyticMotive.reindexing_pullback_eq
    M.compactGeometric f g R

/-- Left identity for pullbacks carried by the stabilized component. -/
theorem stabilized_left_identity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (stabilizedTransferAction M).act
        (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (stabilizedTransferAction M).act f :=
  FunctorialStabilizedAnalyticMotive.left_identity_pullback_eq
    M.stabilized f

/-- Right identity for pullbacks carried by the stabilized component. -/
theorem stabilized_right_identity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (stabilizedTransferAction M).act
        (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (stabilizedTransferAction M).act f :=
  FunctorialStabilizedAnalyticMotive.right_identity_pullback_eq
    M.stabilized f

/-- Associativity for pullbacks carried by the stabilized component. -/
theorem stabilized_associativity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (stabilizedTransferAction M).act
        (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (stabilizedTransferAction M).act
        (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialStabilizedAnalyticMotive.associativity_pullback_eq
    M.stabilized f g h

/-- Left identity for pullbacks carried by the compact-geometric component. -/
theorem compact_left_identity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactTransferAction M).act
        (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (compactTransferAction M).act f :=
  FunctorialCompactGeometricAnalyticMotive.left_identity_pullback_eq
    M.compactGeometric f

/-- Right identity for pullbacks carried by the compact-geometric component. -/
theorem compact_right_identity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactTransferAction M).act
        (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (compactTransferAction M).act f :=
  FunctorialCompactGeometricAnalyticMotive.right_identity_pullback_eq
    M.compactGeometric f

/-- Associativity for pullbacks carried by the compact-geometric component. -/
theorem compact_associativity_pullback_eq
    (M : FunctorialCompactAnalyticMotive)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (compactTransferAction M).act
        (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (compactTransferAction M).act
        (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialCompactGeometricAnalyticMotive.associativity_pullback_eq
    M.compactGeometric f g h

end FunctorialCompactAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
