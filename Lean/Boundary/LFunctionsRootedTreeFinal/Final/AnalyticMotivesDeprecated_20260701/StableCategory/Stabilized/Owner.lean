import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.StableCategory.Effective.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.Owner

/-!
# Tate-stabilized analytic motive category

This file owns the category obtained from the effective analytic motive
category by Tate stabilization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
The Tate-stabilized analytic motive layer, obtained from the effective layer by
equipping it with Tate-stabilized presheaf data.
-/
structure StabilizedAnalyticMotive where
  effective : EffectiveAnalyticMotive
  stabilizedPresheaf : TateStabilizedAnalyticPresheaf

namespace StabilizedAnalyticMotive

/-- The effective motive underlying a stabilized analytic motive. -/
def effectivePart (M : StabilizedAnalyticMotive) :
    EffectiveAnalyticMotive :=
  M.effective

/-- The Tate-stabilized presheaf carried by a stabilized analytic motive. -/
def stabilized (M : StabilizedAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.stabilizedPresheaf

/-- The interval-local presheaf underlying the effective part. -/
def effectivePresheaf (M : StabilizedAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.effective.intervalLocalPresheaf

/-- The interval-local presheaf underlying the stabilized presheaf. -/
def stabilizedUnderlying (M : StabilizedAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.stabilizedPresheaf.presheaf

/-- The analytic Tate object selected by a stabilized analytic motive. -/
def tate (M : StabilizedAnalyticMotive) :
    AnalyticTateObject :=
  M.stabilizedPresheaf.tateObject

/-- The inverse Tate shift of the stabilized underlying presheaf. -/
def inverseUnderlying (M : StabilizedAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.stabilizedPresheaf.inverseUnderlying

/-- Tensoring the inverse Tate shift recovers the stabilized underlying presheaf. -/
theorem tensor_inverseUnderlying_eq (M : StabilizedAnalyticMotive) :
    M.stabilizedPresheaf.tensorAction.tensorObject M.inverseUnderlying =
      M.stabilizedPresheaf.presheaf :=
  TateStabilizedAnalyticPresheaf.tensor_inverseUnderlying_eq
    M.stabilizedPresheaf

end StabilizedAnalyticMotive

/--
The Tate-stabilized analytic motive layer carrying functorial rational
transfer laws.
-/
structure FunctorialStabilizedAnalyticMotive where
  effective : EffectiveAnalyticMotive
  stabilizedPresheaf : FunctorialTateStabilizedAnalyticPresheaf

namespace FunctorialStabilizedAnalyticMotive

/-- Forget functorial transfer laws from a stabilized analytic motive. -/
def forget (M : FunctorialStabilizedAnalyticMotive) :
    StabilizedAnalyticMotive where
  effective := M.effective
  stabilizedPresheaf := M.stabilizedPresheaf.forget

/-- The effective motive underlying a functorial stabilized analytic motive. -/
def effectivePart (M : FunctorialStabilizedAnalyticMotive) :
    EffectiveAnalyticMotive :=
  M.effective

/-- The functorial Tate-stabilized presheaf carried by the motive. -/
def stabilized (M : FunctorialStabilizedAnalyticMotive) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  M.stabilizedPresheaf

/-- The interval-local presheaf underlying the effective part. -/
def effectivePresheaf (M : FunctorialStabilizedAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.effective.intervalLocalPresheaf

/-- The functorial interval-local presheaf underlying the stabilized presheaf. -/
def stabilizedUnderlying (M : FunctorialStabilizedAnalyticMotive) :
    FunctorialIntervalLocalAnalyticPresheaf :=
  M.stabilizedPresheaf.presheaf

/-- The analytic Tate object selected by a functorial stabilized analytic motive. -/
def tate (M : FunctorialStabilizedAnalyticMotive) :
    AnalyticTateObject :=
  M.stabilizedPresheaf.tateObject

/-- The inverse Tate shift of the forgotten stabilized underlying presheaf. -/
def inverseUnderlying (M : FunctorialStabilizedAnalyticMotive) :
    IntervalLocalAnalyticPresheaf :=
  M.stabilizedPresheaf.inverseUnderlying

/-- Tensoring the inverse Tate shift recovers the forgotten stabilized presheaf. -/
theorem tensor_inverseUnderlying_eq
    (M : FunctorialStabilizedAnalyticMotive) :
    M.stabilizedPresheaf.tensorAction.tensorObject M.inverseUnderlying =
      M.stabilizedPresheaf.presheaf.forget :=
  FunctorialTateStabilizedAnalyticPresheaf.tensor_inverseUnderlying_eq
    M.stabilizedPresheaf

/-- The transfer action retained by a functorial stabilized analytic motive. -/
def transferAction (M : FunctorialStabilizedAnalyticMotive) :
    RationalContourTransferAction
      (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialTateStabilizedAnalyticPresheaf.transferAction
    M.stabilizedPresheaf

/--
Reindexing invariance for pullbacks carried by a functorial stabilized
analytic motive.
-/
theorem reindexing_pullback_eq
    (M : FunctorialStabilizedAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction M).act f = (transferAction M).act g :=
  FunctorialTateStabilizedAnalyticPresheaf.reindexing_pullback_eq
    M.stabilizedPresheaf f g R

/-- Left identity for pullbacks carried by a functorial stabilized analytic motive. -/
theorem left_identity_pullback_eq
    (M : FunctorialStabilizedAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction M).act
        (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction M).act f :=
  FunctorialTateStabilizedAnalyticPresheaf.left_identity_pullback_eq
    M.stabilizedPresheaf f

/-- Right identity for pullbacks carried by a functorial stabilized analytic motive. -/
theorem right_identity_pullback_eq
    (M : FunctorialStabilizedAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction M).act
        (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction M).act f :=
  FunctorialTateStabilizedAnalyticPresheaf.right_identity_pullback_eq
    M.stabilizedPresheaf f

/-- Associativity for pullbacks carried by a functorial stabilized analytic motive. -/
theorem associativity_pullback_eq
    (M : FunctorialStabilizedAnalyticMotive)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction M).act
        (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction M).act
        (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialTateStabilizedAnalyticPresheaf.associativity_pullback_eq
    M.stabilizedPresheaf f g h

end FunctorialStabilizedAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
