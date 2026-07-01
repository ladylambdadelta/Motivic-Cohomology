import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ConservativeGenerators.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.Covers.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.CechObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.LocalEquivalences.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.LocalObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.DescentLocalization.ContourCorQConstruction.Owner
import Mathlib.CategoryTheory.Localization.HasLocalization
import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Descent localization for contour-transfer presheaves

The descent topology is generated from controlled analytic covers: contour
refinements and analytified algebraic descent data.  This keeps the comparison
with `DM_gm(ℚ)_ℚ` tied to a conservative cover calculus.

Dependency order: conservative generators, covers, Cech objects, local
equivalences, then local objects.

Foundational sources: mathlib's localization and sheaf APIs provide the
categorical language for descent localization.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A presheaf with contour transfers equipped with descent-locality data for the
conservative contour descent cover calculus.
-/
structure DescentLocalAnalyticPresheaf where
  presheafWithTransfers : AnalyticPresheafWithTransfers
  descentLocality : ContourDescentLocalObject presheafWithTransfers

namespace DescentLocalAnalyticPresheaf

/-- The underlying presheaf with contour transfers. -/
def underlying (F : DescentLocalAnalyticPresheaf) :
    AnalyticPresheafWithTransfers :=
  F.presheafWithTransfers

/-- The descent-locality data carried by a descent-local analytic presheaf. -/
def locality (F : DescentLocalAnalyticPresheaf) :
    ContourDescentLocalObject F.presheafWithTransfers :=
  F.descentLocality

end DescentLocalAnalyticPresheaf

/--
A functorial presheaf with contour transfers equipped with descent-locality
data.  This is the descent-local layer that retains the rational transfer
identity and composition laws.
-/
structure FunctorialDescentLocalAnalyticPresheaf where
  presheafWithTransfers : FunctorialAnalyticPresheafWithTransfers
  descentLocality :
    FunctorialContourDescentLocalObject presheafWithTransfers

namespace FunctorialDescentLocalAnalyticPresheaf

/-- Forget functoriality laws from a functorial descent-local presheaf. -/
def forget (F : FunctorialDescentLocalAnalyticPresheaf) :
    DescentLocalAnalyticPresheaf where
  presheafWithTransfers := F.presheafWithTransfers.forget
  descentLocality := F.descentLocality.localObject

/-- The functorial presheaf with transfers before descent localization. -/
def underlyingFunctorial (F : FunctorialDescentLocalAnalyticPresheaf) :
    FunctorialAnalyticPresheafWithTransfers :=
  F.presheafWithTransfers

/-- The transfer action retained after descent localization. -/
def transferAction (F : FunctorialDescentLocalAnalyticPresheaf) :
    RationalContourTransferAction F.presheafWithTransfers.presheaf :=
  F.presheafWithTransfers.functorialTransfer.transferAction

/--
Reindexing invariance for pullbacks after descent localization, inherited from
the underlying functorial presheaf with transfers.
-/
theorem reindexing_pullback_eq
    (F : FunctorialDescentLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    (transferAction F).act f = (transferAction F).act g :=
  FunctorialAnalyticPresheafWithTransfers.reindexing_pullback_eq
    F.presheafWithTransfers f g R

/--
Left identity for pullbacks after descent localization, inherited from the
underlying functorial presheaf with transfers.
-/
theorem left_identity_pullback_eq
    (F : FunctorialDescentLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.presheafWithTransfers.functorialTransfer.rationalCategory.identity X)
          f) =
      (transferAction F).act f :=
  FunctorialAnalyticPresheafWithTransfers.left_identity_pullback_eq
    F.presheafWithTransfers f

/--
Right identity for pullbacks after descent localization, inherited from the
underlying functorial presheaf with transfers.
-/
theorem right_identity_pullback_eq
    (F : FunctorialDescentLocalAnalyticPresheaf)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    (transferAction F).act
        (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.presheafWithTransfers.functorialTransfer.rationalCategory.identity Y)) =
      (transferAction F).act f :=
  FunctorialAnalyticPresheafWithTransfers.right_identity_pullback_eq
    F.presheafWithTransfers f

/--
Associativity for pullbacks after descent localization, inherited from the
underlying functorial presheaf with transfers.
-/
theorem associativity_pullback_eq
    (F : FunctorialDescentLocalAnalyticPresheaf)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    (transferAction F).act
        (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose
          (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            f g) h) =
      (transferAction F).act
        (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose f
          (F.presheafWithTransfers.functorialTransfer.rationalCategory.compose
            g h)) :=
  FunctorialAnalyticPresheafWithTransfers.associativity_pullback_eq
    F.presheafWithTransfers f g h

end FunctorialDescentLocalAnalyticPresheaf

end AnalyticMotives
end LFunctions
end Boundary
