import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.IntervalLocalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.TateObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.TensorAction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.Inversion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.ContourCorQConstruction.Owner

/-!
# Tate stabilization for analytic motives

Tate stabilization is downstream of descent and interval localization.  The
Tate object is an analytic bulk object with contour transfer behavior, not a
weight label extracted from a trace realization.

Dependency order: Tate object, tensor action, then inversion.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
An interval-local analytic presheaf equipped with analytic Tate stabilization
data: a Tate object, its tensor action, and inversion data for that action.
-/
structure TateStabilizedAnalyticPresheaf where
  presheaf : IntervalLocalAnalyticPresheaf
  tateObject : AnalyticTateObject
  tensorAction : AnalyticTateTensorAction tateObject
  inversion : AnalyticTateInversion tensorAction

namespace TateStabilizedAnalyticPresheaf

/-- The underlying interval-local analytic presheaf. -/
def underlying (F : TateStabilizedAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  F.presheaf

/-- The analytic Tate object selected in a stabilized presheaf package. -/
def tate (F : TateStabilizedAnalyticPresheaf) :
    AnalyticTateObject :=
  F.tateObject

/-- The tensor action by the selected analytic Tate object. -/
def action (F : TateStabilizedAnalyticPresheaf) :
    AnalyticTateTensorAction F.tateObject :=
  F.tensorAction

/-- The inversion data for the selected analytic Tate action. -/
def inversionData (F : TateStabilizedAnalyticPresheaf) :
    AnalyticTateInversion F.tensorAction :=
  F.inversion

/-- Tensor the underlying presheaf by the selected analytic Tate object. -/
def tensorUnderlying (F : TateStabilizedAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  F.tensorAction.tensorObject F.presheaf

/-- The inverse Tate shift of the underlying presheaf. -/
def inverseUnderlying (F : TateStabilizedAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  F.inversion.inverseObject F.presheaf

/-- Tensoring the inverse Tate shift recovers the underlying presheaf. -/
theorem tensor_inverseUnderlying_eq (F : TateStabilizedAnalyticPresheaf) :
    F.tensorAction.tensorObject F.inverseUnderlying = F.presheaf :=
  F.inversion.tensorInverse_eq F.presheaf

/-- Inverting the Tate tensor of the underlying presheaf recovers it. -/
theorem inverse_tensorUnderlying_eq (F : TateStabilizedAnalyticPresheaf) :
    F.inversion.inverseObject F.tensorUnderlying = F.presheaf :=
  F.inversion.inverseTensor_eq F.presheaf

end TateStabilizedAnalyticPresheaf

/--
A functorial interval-local analytic presheaf equipped with analytic Tate
stabilization data, retaining rational transfer identity and composition laws.
-/
structure FunctorialTateStabilizedAnalyticPresheaf where
  presheaf : FunctorialIntervalLocalAnalyticPresheaf
  tateObject : AnalyticTateObject
  tensorAction : AnalyticTateTensorAction tateObject
  inversion : AnalyticTateInversion tensorAction

namespace FunctorialTateStabilizedAnalyticPresheaf

/-- Forget functoriality laws from a functorial Tate-stabilized presheaf. -/
def forget (F : FunctorialTateStabilizedAnalyticPresheaf) :
    TateStabilizedAnalyticPresheaf where
  presheaf := F.presheaf.forget
  tateObject := F.tateObject
  tensorAction := F.tensorAction
  inversion := F.inversion

/-- The underlying functorial interval-local analytic presheaf. -/
def underlyingFunctorial (F : FunctorialTateStabilizedAnalyticPresheaf) :
    FunctorialIntervalLocalAnalyticPresheaf :=
  F.presheaf

/-- The analytic Tate object selected by a functorial Tate-stabilized presheaf. -/
def tate (F : FunctorialTateStabilizedAnalyticPresheaf) :
    AnalyticTateObject :=
  F.tateObject

/-- The tensor action selected by a functorial Tate-stabilized presheaf. -/
def action (F : FunctorialTateStabilizedAnalyticPresheaf) :
    AnalyticTateTensorAction F.tateObject :=
  F.tensorAction

/-- The inversion data selected by a functorial Tate-stabilized presheaf. -/
def inversionData (F : FunctorialTateStabilizedAnalyticPresheaf) :
    AnalyticTateInversion F.tensorAction :=
  F.inversion

/-- Tensor the forgotten underlying presheaf by the selected analytic Tate object. -/
def tensorUnderlying (F : FunctorialTateStabilizedAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  F.tensorAction.tensorObject F.presheaf.forget

/-- The inverse Tate shift of the forgotten underlying presheaf. -/
def inverseUnderlying (F : FunctorialTateStabilizedAnalyticPresheaf) :
    IntervalLocalAnalyticPresheaf :=
  F.inversion.inverseObject F.presheaf.forget

/-- Tensoring the inverse Tate shift recovers the forgotten underlying presheaf. -/
theorem tensor_inverseUnderlying_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf) :
    F.tensorAction.tensorObject F.inverseUnderlying = F.presheaf.forget :=
  F.inversion.tensorInverse_eq F.presheaf.forget

/-- Inverting the Tate tensor of the forgotten underlying presheaf recovers it. -/
theorem inverse_tensorUnderlying_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf) :
    F.inversion.inverseObject F.tensorUnderlying = F.presheaf.forget :=
  F.inversion.inverseTensor_eq F.presheaf.forget

/-- The transfer action retained after Tate stabilization. -/
def transferAction (F : FunctorialTateStabilizedAnalyticPresheaf) :
    RationalContourTransferAction
      F.presheaf.descentLocal.presheafWithTransfers.presheaf :=
  FunctorialIntervalLocalAnalyticPresheaf.transferAction F.presheaf

/--
Reindexing invariance for pullbacks after Tate stabilization, inherited from
the underlying functorial interval-local presheaf.
-/
theorem reindexing_pullback_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction F).act f = (transferAction F).act g :=
  FunctorialIntervalLocalAnalyticPresheaf.reindexing_pullback_eq
    F.presheaf f g R

/--
Left identity for pullbacks after Tate stabilization, inherited from the
underlying functorial interval-local presheaf.
-/
theorem left_identity_pullback_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction F).act f :=
  FunctorialIntervalLocalAnalyticPresheaf.left_identity_pullback_eq
    F.presheaf f

/--
Right identity for pullbacks after Tate stabilization, inherited from the
underlying functorial interval-local presheaf.
-/
theorem right_identity_pullback_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction F).act f :=
  FunctorialIntervalLocalAnalyticPresheaf.right_identity_pullback_eq
    F.presheaf f

/--
Associativity for pullbacks after Tate stabilization, inherited from the
underlying functorial interval-local presheaf.
-/
theorem associativity_pullback_eq
    (F : FunctorialTateStabilizedAnalyticPresheaf)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction F).act
        (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction F).act
        (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialIntervalLocalAnalyticPresheaf.associativity_pullback_eq
    F.presheaf f g h

end FunctorialTateStabilizedAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
