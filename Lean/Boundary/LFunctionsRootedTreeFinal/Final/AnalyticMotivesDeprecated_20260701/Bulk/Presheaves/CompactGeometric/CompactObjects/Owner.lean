import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.TateStabilization.Owner

/-!
# Compact generators after Tate stabilization

This file owns compact analytic generators after descent, interval
localization, and Tate stabilization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A compact analytic generator after descent, interval localization, and Tate
stabilization.  The generator is represented by a stabilized presheaf together
with the contour-admissible bulk it is generated from.
-/
structure CompactAnalyticGenerator where
  sourceBulk : ContourAdmissibleBulk
  stabilizedPresheaf : TateStabilizedAnalyticPresheaf

namespace CompactAnalyticGenerator

/-- The contour-admissible bulk underlying a compact analytic generator. -/
def source (G : CompactAnalyticGenerator) : ContourAdmissibleBulk :=
  G.sourceBulk

/-- The Tate-stabilized presheaf carried by a compact analytic generator. -/
def stabilized (G : CompactAnalyticGenerator) :
    TateStabilizedAnalyticPresheaf :=
  G.stabilizedPresheaf

/-- The source bulk core of a compact analytic generator. -/
def sourceCore (G : CompactAnalyticGenerator) :
    AnalyticBulkCore :=
  G.sourceBulk.core

/-- The underlying interval-local presheaf of a compact analytic generator. -/
def underlyingPresheaf (G : CompactAnalyticGenerator) :
    IntervalLocalAnalyticPresheaf :=
  G.stabilizedPresheaf.presheaf

/-- The analytic Tate object selected by a compact analytic generator. -/
def tate (G : CompactAnalyticGenerator) :
    AnalyticTateObject :=
  G.stabilizedPresheaf.tateObject

/-- The inverse Tate shift of the generator's underlying presheaf. -/
def inverseUnderlying (G : CompactAnalyticGenerator) :
    IntervalLocalAnalyticPresheaf :=
  G.stabilizedPresheaf.inverseUnderlying

/-- Tensoring the inverse Tate shift recovers the generator's underlying presheaf. -/
theorem tensor_inverseUnderlying_eq (G : CompactAnalyticGenerator) :
    G.stabilizedPresheaf.tensorAction.tensorObject G.inverseUnderlying =
      G.stabilizedPresheaf.presheaf :=
  TateStabilizedAnalyticPresheaf.tensor_inverseUnderlying_eq
    G.stabilizedPresheaf

end CompactAnalyticGenerator

/--
A compact analytic generator carrying the functorial rational transfer laws
through Tate stabilization.
-/
structure FunctorialCompactAnalyticGenerator where
  sourceBulk : ContourAdmissibleBulk
  stabilizedPresheaf : FunctorialTateStabilizedAnalyticPresheaf

namespace FunctorialCompactAnalyticGenerator

/-- Forget functoriality laws from a functorial compact analytic generator. -/
def forget (G : FunctorialCompactAnalyticGenerator) :
    CompactAnalyticGenerator where
  sourceBulk := G.sourceBulk
  stabilizedPresheaf := G.stabilizedPresheaf.forget

/-- The contour-admissible bulk underlying a functorial compact analytic generator. -/
def source (G : FunctorialCompactAnalyticGenerator) :
    ContourAdmissibleBulk :=
  G.sourceBulk

/-- The functorial Tate-stabilized presheaf carried by the generator. -/
def stabilized (G : FunctorialCompactAnalyticGenerator) :
    FunctorialTateStabilizedAnalyticPresheaf :=
  G.stabilizedPresheaf

/-- The source bulk core of a functorial compact analytic generator. -/
def sourceCore (G : FunctorialCompactAnalyticGenerator) :
    AnalyticBulkCore :=
  G.sourceBulk.core

/-- The underlying functorial interval-local presheaf of a compact generator. -/
def underlyingFunctorial (G : FunctorialCompactAnalyticGenerator) :
    FunctorialIntervalLocalAnalyticPresheaf :=
  G.stabilizedPresheaf.presheaf

/-- The analytic Tate object selected by a functorial compact generator. -/
def tate (G : FunctorialCompactAnalyticGenerator) :
    AnalyticTateObject :=
  G.stabilizedPresheaf.tateObject

/-- The inverse Tate shift of the forgotten underlying presheaf. -/
def inverseUnderlying (G : FunctorialCompactAnalyticGenerator) :
    IntervalLocalAnalyticPresheaf :=
  G.stabilizedPresheaf.inverseUnderlying

/-- Tensoring the inverse Tate shift recovers the forgotten underlying presheaf. -/
theorem tensor_inverseUnderlying_eq
    (G : FunctorialCompactAnalyticGenerator) :
    G.stabilizedPresheaf.tensorAction.tensorObject G.inverseUnderlying =
      G.stabilizedPresheaf.presheaf.forget :=
  FunctorialTateStabilizedAnalyticPresheaf.tensor_inverseUnderlying_eq
    G.stabilizedPresheaf

/-- The transfer action retained by a functorial compact analytic generator. -/
def transferAction (G : FunctorialCompactAnalyticGenerator) :
    RationalContourTransferAction
      G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.presheaf :=
  FunctorialTateStabilizedAnalyticPresheaf.transferAction
    G.stabilizedPresheaf

/--
Reindexing invariance for pullbacks carried by a functorial compact analytic
generator.
-/
theorem reindexing_pullback_eq
    (G : FunctorialCompactAnalyticGenerator)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction G).act f = (transferAction G).act g :=
  FunctorialTateStabilizedAnalyticPresheaf.reindexing_pullback_eq
    G.stabilizedPresheaf f g R

/-- Left identity for pullbacks carried by a functorial compact analytic generator. -/
theorem left_identity_pullback_eq
    (G : FunctorialCompactAnalyticGenerator)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction G).act
        (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction G).act f :=
  FunctorialTateStabilizedAnalyticPresheaf.left_identity_pullback_eq
    G.stabilizedPresheaf f

/-- Right identity for pullbacks carried by a functorial compact analytic generator. -/
theorem right_identity_pullback_eq
    (G : FunctorialCompactAnalyticGenerator)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction G).act
        (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction G).act f :=
  FunctorialTateStabilizedAnalyticPresheaf.right_identity_pullback_eq
    G.stabilizedPresheaf f

/-- Associativity for pullbacks carried by a functorial compact analytic generator. -/
theorem associativity_pullback_eq
    (G : FunctorialCompactAnalyticGenerator)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction G).act
        (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction G).act
        (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (G.stabilizedPresheaf.presheaf.descentLocal.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialTateStabilizedAnalyticPresheaf.associativity_pullback_eq
    G.stabilizedPresheaf f g h

end FunctorialCompactAnalyticGenerator

end AnalyticMotives
end LFunctions
end Boundary
