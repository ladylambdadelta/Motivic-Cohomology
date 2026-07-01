import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Effective.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Stabilized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Compact.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.InfinityCategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.ContourCorQConstruction.Owner

/-!
# Stable infinity category owner path

This directory owns the stable category layer after the bulk construction has
passed through `ℚ`-linear transfers, descent localization, interval
localization, Tate stabilization, and compact geometric completion.

The stable category is built from the bulk/presheaf lane.  It is not the
boundary trace category, and it is not imported by the RH bridge.

Dependency order: effective category, Tate-stabilized category, compact
geometric subcategory, then stable infinity category interface.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The stable analytic motive package assembled from the effective, stabilized,
compact, and stable-infinity-interface layers.
-/
structure StableAnalyticMotivePackage where
  effectiveLayer : EffectiveAnalyticMotive
  stabilizedLayer : StabilizedAnalyticMotive
  compactLayer : CompactAnalyticMotive
  compact_stabilized_eq :
    compactLayer.stabilized = stabilizedLayer
  infinityInterface : AnalyticMotivicStableInfinityInterface

namespace StableAnalyticMotivePackage

/-- The effective layer of the stable analytic motive package. -/
def effective (P : StableAnalyticMotivePackage) :
    EffectiveAnalyticMotive :=
  P.effectiveLayer

/-- The compact layer of the stable analytic motive package. -/
def compact (P : StableAnalyticMotivePackage) :
    CompactAnalyticMotive :=
  P.compactLayer

/-- The stabilized analytic motive layer of the package. -/
def stabilized (P : StableAnalyticMotivePackage) :
    StabilizedAnalyticMotive :=
  P.stabilizedLayer

/-- The Tate-stabilized presheaf carried by the stabilized layer. -/
def stabilizedPresheaf (P : StableAnalyticMotivePackage) :
    TateStabilizedAnalyticPresheaf :=
  P.stabilizedLayer.stabilizedPresheaf

/-- The compact-geometric component of the compact layer. -/
def compactGeometric (P : StableAnalyticMotivePackage) :
    CompactGeometricAnalyticMotive :=
  P.compactLayer.compactGeometric

/-- The compact-geometric closed object of the package. -/
def compactClosedObject (P : StableAnalyticMotivePackage) :
    TateStabilizedAnalyticPresheaf :=
  P.compactLayer.compactClosedObject

/--
The compact-geometric closed object agrees with the package's stabilized
presheaf.
-/
theorem compactGeometric_closedObject_compatibility
    (P : StableAnalyticMotivePackage) :
    P.compactLayer.compactGeometric.thickClosure.closedObject =
      P.stabilizedLayer.stabilizedPresheaf :=
  Eq.trans P.compactLayer.compactGeometric_closedObject_eq
    (congrArg StabilizedAnalyticMotive.stabilizedPresheaf
      P.compact_stabilized_eq)

/-- The stable infinity interface carried by the package. -/
def infinity (P : StableAnalyticMotivePackage) :
    AnalyticMotivicStableInfinityInterface :=
  P.infinityInterface

end StableAnalyticMotivePackage

/--
The stable analytic motive package carrying functorial rational transfer laws
through the stabilized and compact layers.
-/
structure FunctorialStableAnalyticMotivePackage where
  effectiveLayer : EffectiveAnalyticMotive
  stabilizedLayer : FunctorialStabilizedAnalyticMotive
  compactLayer : FunctorialCompactAnalyticMotive
  compact_stabilized_eq :
    compactLayer.stabilized = stabilizedLayer
  infinityInterface : AnalyticMotivicStableInfinityInterface

namespace FunctorialStableAnalyticMotivePackage

/-- Forget functorial transfer laws from the stable analytic motive package. -/
def forget (P : FunctorialStableAnalyticMotivePackage) :
    StableAnalyticMotivePackage where
  effectiveLayer := P.effectiveLayer
  stabilizedLayer := P.stabilizedLayer.forget
  compactLayer := P.compactLayer.forget
  compact_stabilized_eq :=
    congrArg FunctorialStabilizedAnalyticMotive.forget
      P.compact_stabilized_eq
  infinityInterface := P.infinityInterface

/-- The effective layer of the functorial stable analytic motive package. -/
def effective (P : FunctorialStableAnalyticMotivePackage) :
    EffectiveAnalyticMotive :=
  P.effectiveLayer

/-- The functorial compact layer of the package. -/
def compact (P : FunctorialStableAnalyticMotivePackage) :
    FunctorialCompactAnalyticMotive :=
  P.compactLayer

/-- The functorial stabilized analytic motive layer of the package. -/
def stabilized (P : FunctorialStableAnalyticMotivePackage) :
    FunctorialStabilizedAnalyticMotive :=
  P.stabilizedLayer

/-- The functorial Tate-stabilized presheaf carried by the stabilized layer. -/
def stabilizedPresheaf (P : FunctorialStableAnalyticMotivePackage) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  P.stabilizedLayer.stabilizedPresheaf

/-- The functorial compact-geometric component of the compact layer. -/
def compactGeometric (P : FunctorialStableAnalyticMotivePackage) :
    FunctorialCompactGeometricAnalyticMotive :=
  P.compactLayer.compactGeometric

/-- The functorial compact-geometric closed object of the package. -/
def compactClosedObject (P : FunctorialStableAnalyticMotivePackage) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  P.compactLayer.compactClosedObject

/--
The compact layer's stabilized component agrees with the stabilized layer of
the functorial stable analytic motive package.
-/
theorem compact_stabilized_compatibility
    (P : FunctorialStableAnalyticMotivePackage) :
    P.compactLayer.stabilized = P.stabilizedLayer :=
  P.compact_stabilized_eq

/--
The compact-geometric closed object agrees with the package's functorial
stabilized presheaf.
-/
theorem compactGeometric_closedObject_compatibility
    (P : FunctorialStableAnalyticMotivePackage) :
    P.compactLayer.compactGeometric.functorialThickClosure.closedObject =
      P.stabilizedLayer.stabilizedPresheaf :=
  Eq.trans P.compactLayer.compactGeometric_closedObject_eq
    (congrArg FunctorialStabilizedAnalyticMotive.stabilizedPresheaf
      P.compact_stabilized_eq)

/-- The transfer action retained by the stabilized layer of the package. -/
def stabilizedTransferAction (P : FunctorialStableAnalyticMotivePackage) :
    RationalContourTransferAction
      (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialStabilizedAnalyticMotive.transferAction P.stabilizedLayer

/-- The transfer action retained by the compact layer's stabilized component. -/
def compactStabilizedTransferAction
    (P : FunctorialStableAnalyticMotivePackage) :
    RationalContourTransferAction
      (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialCompactAnalyticMotive.stabilizedTransferAction P.compactLayer

/-- The transfer action retained by the compact layer's compact-geometric component. -/
def compactGeometricTransferAction
    (P : FunctorialStableAnalyticMotivePackage) :
    RationalContourTransferAction
      (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialCompactAnalyticMotive.compactTransferAction P.compactLayer

/--
Reindexing invariance for pullbacks carried by the stabilized layer of the
stable analytic motive package.
-/
theorem stabilized_reindexing_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (stabilizedTransferAction P).act f =
      (stabilizedTransferAction P).act g :=
  FunctorialStabilizedAnalyticMotive.reindexing_pullback_eq
    P.stabilizedLayer f g R

/--
Reindexing invariance for pullbacks carried by the compact layer's stabilized
component.
-/
theorem compact_stabilized_reindexing_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (compactStabilizedTransferAction P).act f =
      (compactStabilizedTransferAction P).act g :=
  FunctorialCompactAnalyticMotive.stabilized_reindexing_pullback_eq
    P.compactLayer f g R

/--
Reindexing invariance for pullbacks carried by the compact layer's
compact-geometric component.
-/
theorem compact_geometric_reindexing_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (compactGeometricTransferAction P).act f =
      (compactGeometricTransferAction P).act g :=
  FunctorialCompactAnalyticMotive.compact_reindexing_pullback_eq
    P.compactLayer f g R

/-- Left identity for pullbacks carried by the stabilized layer. -/
theorem stabilized_left_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (stabilizedTransferAction P).act
        (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (stabilizedTransferAction P).act f :=
  FunctorialStabilizedAnalyticMotive.left_identity_pullback_eq
    P.stabilizedLayer f

/-- Right identity for pullbacks carried by the stabilized layer. -/
theorem stabilized_right_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (stabilizedTransferAction P).act
        (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (stabilizedTransferAction P).act f :=
  FunctorialStabilizedAnalyticMotive.right_identity_pullback_eq
    P.stabilizedLayer f

/-- Associativity for pullbacks carried by the stabilized layer. -/
theorem stabilized_associativity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (stabilizedTransferAction P).act
        (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (stabilizedTransferAction P).act
        (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.stabilizedLayer.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialStabilizedAnalyticMotive.associativity_pullback_eq
    P.stabilizedLayer f g h

/-- Left identity for pullbacks carried by the compact layer's stabilized component. -/
theorem compact_stabilized_left_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactStabilizedTransferAction P).act
        (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (compactStabilizedTransferAction P).act f :=
  FunctorialCompactAnalyticMotive.stabilized_left_identity_pullback_eq
    P.compactLayer f

/-- Right identity for pullbacks carried by the compact layer's stabilized component. -/
theorem compact_stabilized_right_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactStabilizedTransferAction P).act
        (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (compactStabilizedTransferAction P).act f :=
  FunctorialCompactAnalyticMotive.stabilized_right_identity_pullback_eq
    P.compactLayer f

/-- Associativity for pullbacks carried by the compact layer's stabilized component. -/
theorem compact_stabilized_associativity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (compactStabilizedTransferAction P).act
        (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (compactStabilizedTransferAction P).act
        (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.compactLayer.stabilized.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialCompactAnalyticMotive.stabilized_associativity_pullback_eq
    P.compactLayer f g h

/-- Left identity for pullbacks carried by the compact-geometric component. -/
theorem compact_geometric_left_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactGeometricTransferAction P).act
        (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (compactGeometricTransferAction P).act f :=
  FunctorialCompactAnalyticMotive.compact_left_identity_pullback_eq
    P.compactLayer f

/-- Right identity for pullbacks carried by the compact-geometric component. -/
theorem compact_geometric_right_identity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (compactGeometricTransferAction P).act
        (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (compactGeometricTransferAction P).act f :=
  FunctorialCompactAnalyticMotive.compact_right_identity_pullback_eq
    P.compactLayer f

/-- Associativity for pullbacks carried by the compact-geometric component. -/
theorem compact_geometric_associativity_pullback_eq
    (P : FunctorialStableAnalyticMotivePackage)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (compactGeometricTransferAction P).act
        (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (compactGeometricTransferAction P).act
        (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (P.compactLayer.compactGeometric.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialCompactAnalyticMotive.compact_associativity_pullback_eq
    P.compactLayer f g h

/-- The stable infinity interface carried by the package. -/
def infinity (P : FunctorialStableAnalyticMotivePackage) :
    AnalyticMotivicStableInfinityInterface :=
  P.infinityInterface

end FunctorialStableAnalyticMotivePackage

/--
A functorial stable analytic motive package generated from the bulk
correspondence and presheaf construction.  This records the bridge from the
bulk contour-correspondence lane to the stable infinity-category interface.
-/
structure BulkGeneratedStableAnalyticMotivePackage where
  bulkConstruction : BulkAnalyticMotiveConstruction
  stablePackage : FunctorialStableAnalyticMotivePackage
  stabilizedPresheaf_eq :
    stablePackage.stabilizedLayer.stabilizedPresheaf =
      bulkConstruction.presheaves.tate
  compactGeometric_eq :
    stablePackage.compactLayer.compactGeometric =
      bulkConstruction.presheaves.compactGeometric

namespace BulkGeneratedStableAnalyticMotivePackage

/-- The bulk construction generating the stable package. -/
def bulk (P : BulkGeneratedStableAnalyticMotivePackage) :
    BulkAnalyticMotiveConstruction :=
  P.bulkConstruction

/-- The functorial stable package generated from the bulk construction. -/
def stable (P : BulkGeneratedStableAnalyticMotivePackage) :
    FunctorialStableAnalyticMotivePackage :=
  P.stablePackage

/-- The underlying non-functorial stable package. -/
def forget (P : BulkGeneratedStableAnalyticMotivePackage) :
    StableAnalyticMotivePackage :=
  P.stablePackage.forget

/-- The stabilized presheaf of the stable package is the bulk Tate stabilization. -/
theorem stabilizedPresheaf_compatibility
    (P : BulkGeneratedStableAnalyticMotivePackage) :
    P.stablePackage.stabilizedLayer.stabilizedPresheaf =
      P.bulkConstruction.presheaves.tate :=
  P.stabilizedPresheaf_eq

/--
The compact-geometric component of the stable package is the bulk compact
geometric construction.
-/
theorem compactGeometric_compatibility
    (P : BulkGeneratedStableAnalyticMotivePackage) :
    P.stablePackage.compactLayer.compactGeometric =
      P.bulkConstruction.presheaves.compactGeometric :=
  P.compactGeometric_eq

/-- The rational category used by the generated stable package. -/
def rationalCategory (P : BulkGeneratedStableAnalyticMotivePackage) :
    RationalContourCategoryData :=
  P.bulkConstruction.rationalCategory

/-- The correspondence calculus used by the generated stable package. -/
def correspondenceCalculus
    (P : BulkGeneratedStableAnalyticMotivePackage) :
    ContourCorrespondenceCalculus :=
  P.bulkConstruction.correspondenceCalculus

/--
The generated stable package uses rational transfers linearized from the bulk
correspondence calculus.
-/
theorem rational_correspondenceLaws_compatibility
    (P : BulkGeneratedStableAnalyticMotivePackage) :
    P.rationalCategory.correspondenceLaws =
      P.correspondenceCalculus.laws :=
  BulkAnalyticMotiveConstruction.rational_correspondenceLaws_compatibility
    P.bulkConstruction

/-- The transfer action inherited from the bulk construction. -/
def bulkTransferAction (P : BulkGeneratedStableAnalyticMotivePackage) :
    RationalContourTransferAction
      P.bulkConstruction.presheaves.transfers.presheaf :=
  P.bulkConstruction.transferAction

/-- Reindexing invariance for the transfer action inherited from the bulk. -/
theorem bulk_reindexing_pullback_eq
    (P : BulkGeneratedStableAnalyticMotivePackage)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (P.bulkTransferAction).act f =
      (P.bulkTransferAction).act g :=
  BulkAnalyticMotiveConstruction.reindexing_pullback_eq
    P.bulkConstruction f g R

end BulkGeneratedStableAnalyticMotivePackage

end AnalyticMotives
end LFunctions
end Boundary
