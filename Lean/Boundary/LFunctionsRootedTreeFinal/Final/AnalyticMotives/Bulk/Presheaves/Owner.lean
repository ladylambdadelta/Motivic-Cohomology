import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Correspondences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.Owner

/-!
# Presheaves with analytic contour transfers

This directory owns the passage from contour-compatible correspondences to the
stable analytic-motive category:

1. `ℚ`-linear presheaves with transfers;
2. descent localization;
3. interval localization;
4. Tate stabilization;
5. compact geometric/idempotent-complete subcategory.

Trace realizations consume this layer after it is constructed.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The assembled presheaf-side analytic motive construction.  The fields follow
the dependency order from rational contour transfers through descent,
interval-localization, Tate stabilization, and the compact geometric layer.
-/
structure AnalyticPresheafConstruction where
  transfers : AnalyticPresheafWithTransfers
  descent : DescentLocalAnalyticPresheaf
  interval : IntervalLocalAnalyticPresheaf
  tate : TateStabilizedAnalyticPresheaf
  compactGeometric : CompactGeometricAnalyticMotive
  descent_transfers_eq :
    descent.presheafWithTransfers = transfers
  interval_descent_eq :
    interval.descentLocal = descent
  tate_interval_eq :
    tate.presheaf = interval
  compact_closed_eq :
    compactGeometric.closedObject = tate

namespace AnalyticPresheafConstruction

/-- The rational contour presheaf at the base of the assembled construction. -/
def rationalPresheaf (C : AnalyticPresheafConstruction) :
    RationalContourPresheaf :=
  C.transfers.presheaf

/-- The transfer action at the base of the assembled construction. -/
def transferAction (C : AnalyticPresheafConstruction) :
    RationalContourTransferAction C.transfers.presheaf :=
  C.transfers.transferAction

/-- The descent-locality data in the assembled construction. -/
def descentLocality (C : AnalyticPresheafConstruction) :
    ContourDescentLocalObject C.descent.presheafWithTransfers :=
  C.descent.descentLocality

/-- The interval-locality data in the assembled construction. -/
def intervalLocality (C : AnalyticPresheafConstruction) :
    IntervalLocalObject C.interval.descentLocal :=
  C.interval.intervalLocality

/-- The analytic Tate object used for stabilization. -/
def tateObject (C : AnalyticPresheafConstruction) :
    AnalyticTateObject :=
  C.tate.tateObject

/-- The tensor action by the analytic Tate object. -/
def tateTensorAction (C : AnalyticPresheafConstruction) :
    AnalyticTateTensorAction C.tate.tateObject :=
  C.tate.tensorAction

/-- The Tate inversion data in the assembled construction. -/
def tateInversion (C : AnalyticPresheafConstruction) :
    AnalyticTateInversion C.tate.tensorAction :=
  C.tate.inversion

/-- The thick closure component of the compact geometric layer. -/
def compactThickClosure (C : AnalyticPresheafConstruction) :
    CompactAnalyticThickClosure :=
  C.compactGeometric.thickClosure

/-- The idempotent completion component of the compact geometric layer. -/
def compactIdempotentCompletion (C : AnalyticPresheafConstruction) :
    CompactAnalyticIdempotentCompletion :=
  C.compactGeometric.idempotentCompletion

/-- The compact-geometric closed object agrees with the assembled Tate object. -/
theorem compact_closedObject_eq_tate
    (C : AnalyticPresheafConstruction) :
    C.compactGeometric.closedObject = C.tate :=
  C.compact_closed_eq

end AnalyticPresheafConstruction

/--
The assembled functorial presheaf-side analytic motive construction.  This
retains the rational contour transfer identity, composition, and reindexing
laws through the same construction chain.
-/
structure FunctorialAnalyticPresheafConstruction where
  transfers : FunctorialAnalyticPresheafWithTransfers
  descent : FunctorialDescentLocalAnalyticPresheaf
  interval : FunctorialIntervalLocalAnalyticPresheaf
  tate : FunctorialTateStabilizedAnalyticPresheaf
  compactGeometric : FunctorialCompactGeometricAnalyticMotive
  descent_transfers_eq :
    descent.presheafWithTransfers = transfers
  interval_descent_eq :
    interval.descentLocal = descent
  tate_interval_eq :
    tate.presheaf = interval
  compact_closed_eq :
    compactGeometric.closedObject = tate

namespace FunctorialAnalyticPresheafConstruction

/-- Forget functorial transfer laws from the assembled construction. -/
def forget (C : FunctorialAnalyticPresheafConstruction) :
    AnalyticPresheafConstruction where
  transfers := C.transfers.forget
  descent := C.descent.forget
  interval := C.interval.forget
  tate := C.tate.forget
  compactGeometric := C.compactGeometric.forget
  descent_transfers_eq :=
    congrArg FunctorialAnalyticPresheafWithTransfers.forget
      C.descent_transfers_eq
  interval_descent_eq :=
    congrArg FunctorialDescentLocalAnalyticPresheaf.forget
      C.interval_descent_eq
  tate_interval_eq :=
    congrArg FunctorialIntervalLocalAnalyticPresheaf.forget
      C.tate_interval_eq
  compact_closed_eq :=
    congrArg FunctorialTateStabilizedAnalyticPresheaf.forget
      C.compact_closed_eq

/-- The rational contour category laws used by the assembled construction. -/
def categoryData (C : FunctorialAnalyticPresheafConstruction) :
    RationalContourCategoryData :=
  C.transfers.categoryData

/-- The transfer action retained by the assembled functorial construction. -/
def transferAction (C : FunctorialAnalyticPresheafConstruction) :
    RationalContourTransferAction C.transfers.presheaf :=
  C.transfers.functorialTransfer.transferAction

/--
Reindexing invariance for pullbacks in the assembled functorial construction.
-/
theorem reindexing_pullback_eq
    (C : FunctorialAnalyticPresheafConstruction)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction C).act f = (transferAction C).act g :=
  FunctorialAnalyticPresheafWithTransfers.reindexing_pullback_eq
    C.transfers f g R

/-- Left identity for pullbacks in the assembled functorial construction. -/
theorem left_identity_pullback_eq
    (C : FunctorialAnalyticPresheafConstruction)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction C).act
        (C.categoryData.compose (C.categoryData.identity X) f) =
      (transferAction C).act f :=
  FunctorialAnalyticPresheafWithTransfers.left_identity_pullback_eq
    C.transfers f

/-- Right identity for pullbacks in the assembled functorial construction. -/
theorem right_identity_pullback_eq
    (C : FunctorialAnalyticPresheafConstruction)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction C).act
        (C.categoryData.compose f (C.categoryData.identity Y)) =
      (transferAction C).act f :=
  FunctorialAnalyticPresheafWithTransfers.right_identity_pullback_eq
    C.transfers f

/-- Associativity for pullbacks in the assembled functorial construction. -/
theorem associativity_pullback_eq
    (C : FunctorialAnalyticPresheafConstruction)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction C).act
        (C.categoryData.compose (C.categoryData.compose f g) h) =
      (transferAction C).act
        (C.categoryData.compose f (C.categoryData.compose g h)) :=
  FunctorialAnalyticPresheafWithTransfers.associativity_pullback_eq
    C.transfers f g h

end FunctorialAnalyticPresheafConstruction

end AnalyticMotives
end LFunctions
end Boundary
