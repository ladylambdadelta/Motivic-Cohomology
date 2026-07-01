import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.IntervalParameter.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.IntervalObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.HomotopyEquivalences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.LocalObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.ContourCorQConstruction.Owner

/-!
# Interval localization for contour-transfer presheaves

Interval localization is downstream of descent and upstream of Tate
stabilization.  The interval object is part of the analytic bulk calculus and
is compared later with the algebraic `𝔸¹` interval.

Dependency order: interval parameter, interval object, homotopy equivalences,
then interval-local objects.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A descent-local analytic presheaf equipped with interval-locality data.  This
is the presheaf layer immediately upstream of Tate stabilization.
-/
structure IntervalLocalAnalyticPresheaf where
  descentLocal : DescentLocalAnalyticPresheaf
  intervalLocality : IntervalLocalObject descentLocal

namespace IntervalLocalAnalyticPresheaf

/-- The underlying descent-local analytic presheaf. -/
def underlying (F : IntervalLocalAnalyticPresheaf) :
    DescentLocalAnalyticPresheaf :=
  F.descentLocal

/-- The interval-locality data carried by an interval-local presheaf. -/
def locality (F : IntervalLocalAnalyticPresheaf) :
    IntervalLocalObject F.descentLocal :=
  F.intervalLocality

end IntervalLocalAnalyticPresheaf

/--
A functorial descent-local analytic presheaf equipped with interval-locality
data.  This is the interval-local layer retaining rational transfer
functoriality.
-/
structure FunctorialIntervalLocalAnalyticPresheaf where
  descentLocal : FunctorialDescentLocalAnalyticPresheaf
  intervalLocality : FunctorialIntervalLocalObject descentLocal

namespace FunctorialIntervalLocalAnalyticPresheaf

/-- Forget functoriality laws from a functorial interval-local presheaf. -/
def forget (F : FunctorialIntervalLocalAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf where
  descentLocal := F.descentLocal.forget
  intervalLocality := F.intervalLocality.localObject

/-- The underlying functorial descent-local analytic presheaf. -/
def underlyingFunctorial (F : FunctorialIntervalLocalAnalyticPresheaf) :
    FunctorialDescentLocalAnalyticPresheaf :=
  F.descentLocal

/-- The transfer action retained after interval localization. -/
def transferAction (F : FunctorialIntervalLocalAnalyticPresheaf) :
    RationalContourTransferAction
      F.descentLocal.presheafWithTransfers.presheaf :=
  FunctorialDescentLocalAnalyticPresheaf.transferAction F.descentLocal

/--
Reindexing invariance for pullbacks after interval localization, inherited
from the underlying functorial descent-local presheaf.
-/
theorem reindexing_pullback_eq
    (F : FunctorialIntervalLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction F).act f = (transferAction F).act g :=
  FunctorialDescentLocalAnalyticPresheaf.reindexing_pullback_eq
    F.descentLocal f g R

/--
Left identity for pullbacks after interval localization, inherited from the
underlying functorial descent-local presheaf.
-/
theorem left_identity_pullback_eq
    (F : FunctorialIntervalLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction F).act f :=
  FunctorialDescentLocalAnalyticPresheaf.left_identity_pullback_eq
    F.descentLocal f

/--
Right identity for pullbacks after interval localization, inherited from the
underlying functorial descent-local presheaf.
-/
theorem right_identity_pullback_eq
    (F : FunctorialIntervalLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction F).act f :=
  FunctorialDescentLocalAnalyticPresheaf.right_identity_pullback_eq
    F.descentLocal f

/--
Associativity for pullbacks after interval localization, inherited from the
underlying functorial descent-local presheaf.
-/
theorem associativity_pullback_eq
    (F : FunctorialIntervalLocalAnalyticPresheaf)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction F).act
        (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction F).act
        (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialDescentLocalAnalyticPresheaf.associativity_pullback_eq
    F.descentLocal f g h

end FunctorialIntervalLocalAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
