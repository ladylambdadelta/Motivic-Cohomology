import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.PresheafCategory.Owner

/-!
# Transfer action on presheaves

This file owns the action of contour-compatible correspondences on presheaves.
Descent and interval localization are downstream from this transfer action.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
Transfer action data for a rational contour presheaf.  It exposes the pullback
operation along formal rational combinations of contour-compatible
correspondences.
-/
structure RationalContourTransferAction
    (F : RationalContourPresheaf) where
  act :
    {X Y : ContourCorrespondenceObject} →
      RationalContourHom X Y → F.value Y → F.value X

namespace RationalContourTransferAction

/-- The transfer action along a rational contour correspondence. -/
def actAlong {F : RationalContourPresheaf}
    (A : RationalContourTransferAction F)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    F.value Y → F.value X :=
  A.act f

/-- The canonical transfer action carried by a rational contour presheaf. -/
def canonical (F : RationalContourPresheaf) :
    RationalContourTransferAction F where
  act := F.pullback

end RationalContourTransferAction

/--
Functorial transfer action for rational contour correspondences.  This records
reindexing invariance and the identity and composition laws for the
contravariant pullback action.
-/
structure RationalContourFunctorialTransferAction
    (F : RationalContourPresheaf) where
  rationalCategory : RationalContourCategoryData
  transferAction : RationalContourTransferAction F
  reindexing_action :
    {X Y : ContourCorrespondenceObject} →
      (f g : RationalContourHom X Y) →
        RationalContourCombinationReindexing f g →
          transferAction.act f = transferAction.act g
  identity_action :
    (X : ContourCorrespondenceObject) →
      transferAction.act (rationalCategory.identity X) =
        fun x => x
  comp_action :
    {X Y Z : ContourCorrespondenceObject} →
      (f : RationalContourHom X Y) →
        (g : RationalContourHom Y Z) →
          transferAction.act (rationalCategory.compose f g) =
            fun z => transferAction.act f (transferAction.act g z)

namespace RationalContourFunctorialTransferAction

/-- The underlying transfer action. -/
def underlying {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F) :
    RationalContourTransferAction F :=
  A.transferAction

/-- The rational contour category data used by a functorial transfer action. -/
def categoryData {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F) :
    RationalContourCategoryData :=
  A.rationalCategory

/-- Reindexing invariance for the transfer action. -/
theorem reindexing_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    {X Y : ContourCorrespondenceObject}
    (f g : RationalContourHom X Y)
    (R : RationalContourCombinationReindexing f g) :
    A.transferAction.act f = A.transferAction.act g :=
  A.reindexing_action f g R

/-- Identity law for the transfer action. -/
theorem identity_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    (X : ContourCorrespondenceObject) :
    A.transferAction.act (A.rationalCategory.identity X) = fun x => x :=
  A.identity_action X

/-- Composition law for the contravariant transfer action. -/
theorem comp_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    {X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom X Y)
    (g : RationalContourHom Y Z) :
    A.transferAction.act (A.rationalCategory.compose f g) =
      fun z => A.transferAction.act f (A.transferAction.act g z) :=
  A.comp_action f g

/--
Left identity for transfer actions, expressed through the rational
reindexing relation on formal contour combinations.
-/
theorem left_identity_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    A.transferAction.act
        (A.rationalCategory.compose
          (A.rationalCategory.identity X) f) =
      A.transferAction.act f :=
  A.reindexing_action
    (A.rationalCategory.compose
      (A.rationalCategory.identity X) f)
    f
    (RationalContourCategoryData.left_identity_reindexing_eq
      A.rationalCategory f)

/--
Right identity for transfer actions, expressed through the rational
reindexing relation on formal contour combinations.
-/
theorem right_identity_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    {X Y : ContourCorrespondenceObject}
    (f : RationalContourHom X Y) :
    A.transferAction.act
        (A.rationalCategory.compose f
          (A.rationalCategory.identity Y)) =
      A.transferAction.act f :=
  A.reindexing_action
    (A.rationalCategory.compose f
      (A.rationalCategory.identity Y))
    f
    (RationalContourCategoryData.right_identity_reindexing_eq
      A.rationalCategory f)

/--
Associativity for transfer actions, expressed through the rational reindexing
relation on formal contour combinations.
-/
theorem associativity_action_eq {F : RationalContourPresheaf}
    (A : RationalContourFunctorialTransferAction F)
    {W X Y Z : ContourCorrespondenceObject}
    (f : RationalContourHom W X)
    (g : RationalContourHom X Y)
    (h : RationalContourHom Y Z) :
    A.transferAction.act
        (A.rationalCategory.compose
          (A.rationalCategory.compose f g) h) =
      A.transferAction.act
        (A.rationalCategory.compose f
          (A.rationalCategory.compose g h)) :=
  A.reindexing_action
    (A.rationalCategory.compose
      (A.rationalCategory.compose f g) h)
    (A.rationalCategory.compose f
      (A.rationalCategory.compose g h))
    (RationalContourCategoryData.associativity_reindexing_eq
      A.rationalCategory f g h)

end RationalContourFunctorialTransferAction

end AnalyticMotives
end LFunctions
end Boundary
