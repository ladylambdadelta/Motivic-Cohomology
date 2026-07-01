import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.CompactObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ThickClosure.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.IdempotentCompletion.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.CompactGeometric.ContourCorQConstruction.Owner

/-!
# Compact geometric analytic motives

This owner is the compact geometric layer after descent, interval localization,
and Tate stabilization.  It is the layer intended for comparison with
`DM_gm(ℚ)_ℚ` by a weight-triangular equivalence.

Dependency order: compact generators, thick closure, then idempotent
completion.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A compact geometric analytic motive after Tate stabilization: a thick closure
of compact analytic generators together with idempotent-completion data.
-/
structure CompactGeometricAnalyticMotive where
  thickClosure : CompactAnalyticThickClosure
  idempotentCompletion : CompactAnalyticIdempotentCompletion

namespace CompactGeometricAnalyticMotive

/-- The thick closure component of a compact geometric analytic motive. -/
def thick (M : CompactGeometricAnalyticMotive) :
    CompactAnalyticThickClosure :=
  M.thickClosure

/-- The idempotent-completion component of a compact geometric analytic motive. -/
def idempotent (M : CompactGeometricAnalyticMotive) :
    CompactAnalyticIdempotentCompletion :=
  M.idempotentCompletion

/-- The closed object of the compact-geometric thick closure. -/
def closedObject (M : CompactGeometricAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.thickClosure.closedObject

/-- The idempotent-completion retract object. -/
def retractObject (M : CompactGeometricAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.idempotentCompletion.retract

/-- A selected compact generator in the compact-geometric thick closure. -/
def generatorAt (M : CompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    CompactAnalyticGenerator :=
  M.thickClosure.generatorAt i

/-- The source bulk of a selected compact-geometric generator. -/
def generatorSource (M : CompactGeometricAnalyticMotive)
    (i : M.thickClosure.GeneratorIndex) :
    ContourAdmissibleBulk :=
  M.thickClosure.generatorSource i

end CompactGeometricAnalyticMotive

/--
A compact geometric analytic motive carrying functorial rational transfer laws
through the compact-generator and thick-closure stages.
-/
structure FunctorialCompactGeometricAnalyticMotive where
  functorialThickClosure : FunctorialCompactAnalyticThickClosure
  idempotentCompletion : CompactAnalyticIdempotentCompletion
  idempotentThickObject_eq :
    idempotentCompletion.thickObject = functorialThickClosure.forget

namespace FunctorialCompactGeometricAnalyticMotive

/-- Forget functorial transfer laws from a functorial compact geometric motive. -/
def forget (M : FunctorialCompactGeometricAnalyticMotive) :
    CompactGeometricAnalyticMotive where
  thickClosure := M.functorialThickClosure.forget
  idempotentCompletion := M.idempotentCompletion

/-- The functorial thick-closure component. -/
def thick (M : FunctorialCompactGeometricAnalyticMotive) :
    FunctorialCompactAnalyticThickClosure :=
  M.functorialThickClosure

/-- The idempotent-completion component. -/
def idempotent (M : FunctorialCompactGeometricAnalyticMotive) :
    CompactAnalyticIdempotentCompletion :=
  M.idempotentCompletion

/-- The functorial closed object of the compact-geometric thick closure. -/
def closedObject (M : FunctorialCompactGeometricAnalyticMotive) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  M.functorialThickClosure.closedObject

/-- The idempotent-completion retract object. -/
def retractObject (M : FunctorialCompactGeometricAnalyticMotive) :
    TateStabilizedAnalyticPresheaf :=
  M.idempotentCompletion.retract

/-- A selected functorial compact generator in the compact-geometric thick closure. -/
def generatorAt (M : FunctorialCompactGeometricAnalyticMotive)
    (i : M.functorialThickClosure.GeneratorIndex) :
    FunctorialCompactAnalyticGenerator :=
  M.functorialThickClosure.generatorAt i

/-- The source bulk of a selected functorial compact-geometric generator. -/
def generatorSource (M : FunctorialCompactGeometricAnalyticMotive)
    (i : M.functorialThickClosure.GeneratorIndex) :
    ContourAdmissibleBulk :=
  M.functorialThickClosure.generatorSource i

/-- The idempotent-completion thick object agrees with the forgotten functorial thick closure. -/
theorem idempotent_thickObject_compatibility
    (M : FunctorialCompactGeometricAnalyticMotive) :
    M.idempotentCompletion.thickObject =
      M.functorialThickClosure.forget :=
  M.idempotentThickObject_eq

/-- The transfer action retained by the functorial thick-closure component. -/
def transferAction (M : FunctorialCompactGeometricAnalyticMotive) :
    RationalContourTransferAction
      (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers).presheaf :=
  FunctorialCompactAnalyticThickClosure.transferAction
    M.functorialThickClosure

/--
Reindexing invariance for pullbacks carried by the functorial thick-closure
component of a compact geometric analytic motive.
-/
theorem reindexing_pullback_eq
    (M : FunctorialCompactGeometricAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction M).act f = (transferAction M).act g :=
  FunctorialCompactAnalyticThickClosure.reindexing_pullback_eq
    M.functorialThickClosure f g R

/-- Left identity for pullbacks carried by a compact geometric analytic motive. -/
theorem left_identity_pullback_eq
    (M : FunctorialCompactGeometricAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction M).act
        (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction M).act f :=
  FunctorialCompactAnalyticThickClosure.left_identity_pullback_eq
    M.functorialThickClosure f

/-- Right identity for pullbacks carried by a compact geometric analytic motive. -/
theorem right_identity_pullback_eq
    (M : FunctorialCompactGeometricAnalyticMotive)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction M).act
        (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction M).act f :=
  FunctorialCompactAnalyticThickClosure.right_identity_pullback_eq
    M.functorialThickClosure f

/-- Associativity for pullbacks carried by a compact geometric analytic motive. -/
theorem associativity_pullback_eq
    (M : FunctorialCompactGeometricAnalyticMotive)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction M).act
        (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction M).act
        (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (M.functorialThickClosure.closedObject.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialCompactAnalyticThickClosure.associativity_pullback_eq
    M.functorialThickClosure f g h

end FunctorialCompactGeometricAnalyticMotive

end AnalyticMotives
end LFunctions
end Boundary
