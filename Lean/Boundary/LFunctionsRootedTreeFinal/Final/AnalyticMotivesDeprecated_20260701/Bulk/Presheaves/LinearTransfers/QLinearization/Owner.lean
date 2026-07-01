import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Bulk.Presheaves.LinearTransfers.CorrespondenceCategory.Owner

/-!
# `ℚ`-linearization of contour correspondences

This file owns the rational linearization of the contour correspondence
category.  Additive presheaves with transfers are downstream from this
linearized category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/--
A finite formal rational linear combination of contour correspondences from
`X` to `Y`.  The index type carries a `Finite` instance, so this is finite data
without requiring decidable equality on the correspondence type.
-/
structure RationalContourCombination
    (X Y : ContourCorrespondenceObject) where
  Index : Type
  finiteIndex : Finite Index
  coefficient : Index → Rat
  correspondence : Index → ContourCorrespondenceHom X Y

namespace RationalContourCombination

/-- The index type of a formal rational combination. -/
def index {X Y : ContourCorrespondenceObject}
    (L : RationalContourCombination X Y) : Type :=
  L.Index

/-- The rational coefficient at an index of a formal combination. -/
def coeffAt {X Y : ContourCorrespondenceObject}
    (L : RationalContourCombination X Y) (i : L.Index) : Rat :=
  L.coefficient i

/-- The contour correspondence at an index of a formal combination. -/
def correspondenceAt {X Y : ContourCorrespondenceObject}
    (L : RationalContourCombination X Y) (i : L.Index) :
    ContourCorrespondenceHom X Y :=
  L.correspondence i

/--
The rational linear combination with one summand and coefficient `1` attached
to a contour correspondence.
-/
def single {X Y : ContourCorrespondenceObject}
    (f : ContourCorrespondenceHom X Y) :
    RationalContourCombination X Y where
  Index := PUnit
  finiteIndex := inferInstance
  coefficient := fun _ => 1
  correspondence := fun _ => f

/--
The rational identity combination obtained from contour-correspondence category
law data.
-/
def identity (L : ContourCorrespondenceCategoryLawData)
    (X : ContourCorrespondenceObject) :
    RationalContourCombination X X :=
  single (L.identityAt X)

/--
Bilinear composition of rational contour combinations induced by
contour-correspondence category law data.
-/
def comp (L : ContourCorrespondenceCategoryLawData)
    {X Y Z : ContourCorrespondenceObject}
    (F : RationalContourCombination X Y)
    (G : RationalContourCombination Y Z) :
    RationalContourCombination X Z where
  Index := F.Index × G.Index
  finiteIndex := inferInstance
  coefficient := fun i => F.coefficient i.1 * G.coefficient i.2
  correspondence := fun i =>
    L.composeAt (F.correspondence i.1) (G.correspondence i.2)

end RationalContourCombination

/--
Reindexing equivalence between two finite rational contour combinations.
This is the native equality notion for formal finite sums before quotienting:
the finite summand set may change, but coefficients and correspondences are
preserved along the reindexing equivalence.
-/
structure RationalContourCombinationReindexing
    {X Y : ContourCorrespondenceObject}
    (F G : RationalContourCombination X Y) where
  indexEquiv : F.Index ≃ G.Index
  coefficient_eq :
    (i : F.Index) →
      F.coefficient i = G.coefficient (indexEquiv i)
  correspondence_eq :
    (i : F.Index) →
      F.correspondence i = G.correspondence (indexEquiv i)

namespace RationalContourCombinationReindexing

/-- The equivalence of index types selected by a rational-combination reindexing. -/
def indexEquivOf {X Y : ContourCorrespondenceObject}
    {F G : RationalContourCombination X Y}
    (R : RationalContourCombinationReindexing F G) :
    F.Index ≃ G.Index :=
  R.indexEquiv

/-- Coefficients are preserved by a rational-combination reindexing. -/
theorem coefficient_eq_of {X Y : ContourCorrespondenceObject}
    {F G : RationalContourCombination X Y}
    (R : RationalContourCombinationReindexing F G)
    (i : F.Index) :
    F.coefficient i = G.coefficient (R.indexEquiv i) :=
  R.coefficient_eq i

/-- Correspondences are preserved by a rational-combination reindexing. -/
theorem correspondence_eq_of {X Y : ContourCorrespondenceObject}
    {F G : RationalContourCombination X Y}
    (R : RationalContourCombinationReindexing F G)
    (i : F.Index) :
    F.correspondence i = G.correspondence (R.indexEquiv i) :=
  R.correspondence_eq i

/-- Reflexive reindexing of a rational contour combination. -/
def refl {X Y : ContourCorrespondenceObject}
    (F : RationalContourCombination X Y) :
    RationalContourCombinationReindexing F F where
  indexEquiv := Equiv.refl F.Index
  coefficient_eq := fun _ => rfl
  correspondence_eq := fun _ => rfl

/-- Reindexing selected by the left identity law for rational combinations. -/
def leftIdentity
    (L : ContourCorrespondenceCategoryLawData)
    {X Y : ContourCorrespondenceObject}
    (F : RationalContourCombination X Y) :
    RationalContourCombinationReindexing
      (RationalContourCombination.comp L
        (RationalContourCombination.identity L X) F)
      F where
  indexEquiv :=
    { toFun := fun i => i.2
      invFun := fun i => (PUnit.unit, i)
      left_inv := fun i => Prod.ext (PUnit.casesOn i.1 rfl) rfl
      right_inv := fun _ => rfl }
  coefficient_eq := fun i => one_mul (F.coefficient i.2)
  correspondence_eq := fun i =>
    L.left_identity_eq (F.correspondence i.2)

/-- Reindexing selected by the right identity law for rational combinations. -/
def rightIdentity
    (L : ContourCorrespondenceCategoryLawData)
    {X Y : ContourCorrespondenceObject}
    (F : RationalContourCombination X Y) :
    RationalContourCombinationReindexing
      (RationalContourCombination.comp L F
        (RationalContourCombination.identity L Y))
      F where
  indexEquiv :=
    { toFun := fun i => i.1
      invFun := fun i => (i, PUnit.unit)
      left_inv := fun i => Prod.ext rfl (PUnit.casesOn i.2 rfl)
      right_inv := fun _ => rfl }
  coefficient_eq := fun i => mul_one (F.coefficient i.1)
  correspondence_eq := fun i =>
    L.right_identity_eq (F.correspondence i.1)

/-- Reindexing selected by the associativity law for rational combinations. -/
def associativity
    (L : ContourCorrespondenceCategoryLawData)
    {W X Y Z : ContourCorrespondenceObject}
    (F : RationalContourCombination W X)
    (G : RationalContourCombination X Y)
    (H : RationalContourCombination Y Z) :
    RationalContourCombinationReindexing
      (RationalContourCombination.comp L
        (RationalContourCombination.comp L F G) H)
      (RationalContourCombination.comp L F
        (RationalContourCombination.comp L G H)) where
  indexEquiv :=
    { toFun := fun i => (i.1.1, (i.1.2, i.2))
      invFun := fun i => ((i.1, i.2.1), i.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  coefficient_eq := fun i =>
    mul_assoc (F.coefficient i.1.1) (G.coefficient i.1.2)
      (H.coefficient i.2)
  correspondence_eq := fun i =>
    L.associativity_eq (F.correspondence i.1.1)
      (G.correspondence i.1.2) (H.correspondence i.2)

end RationalContourCombinationReindexing

/-- The hom type of the rationally linearized contour-correspondence graph. -/
abbrev RationalContourHom
    (X Y : ContourCorrespondenceObject) : Type :=
  RationalContourCombination X Y

/-- The graph obtained by rationally linearizing contour correspondences. -/
def RationalContourGraph : ContourCorrespondenceGraph where
  Obj := ContourCorrespondenceObject
  Hom := RationalContourHom

/--
Rationally linearized contour-correspondence calculus: the linearized graph
together with identity and composition operations induced by the underlying
contour-correspondence category-law data.
-/
structure RationalContourCategoryData where
  correspondenceLaws : ContourCorrespondenceCategoryLawData
  identity :
    (X : ContourCorrespondenceObject) →
      RationalContourHom X X
  compose :
    {X Y Z : ContourCorrespondenceObject} →
      RationalContourHom X Y →
        RationalContourHom Y Z →
          RationalContourHom X Z
  identity_eq :
    (X : ContourCorrespondenceObject) →
      identity X =
        RationalContourCombination.identity correspondenceLaws X
  left_identity_reindexing :
    {X Y : ContourCorrespondenceObject} →
      (F : RationalContourHom X Y) →
        RationalContourCombinationReindexing
          (compose (identity X) F) F
  right_identity_reindexing :
    {X Y : ContourCorrespondenceObject} →
      (F : RationalContourHom X Y) →
        RationalContourCombinationReindexing
          (compose F (identity Y)) F
  associativity_reindexing :
    {W X Y Z : ContourCorrespondenceObject} →
      (F : RationalContourHom W X) →
        (G : RationalContourHom X Y) →
          (H : RationalContourHom Y Z) →
            RationalContourCombinationReindexing
              (compose (compose F G) H)
              (compose F (compose G H))

namespace RationalContourCategoryData

/-- The identity selected by rational contour category data has the owner form. -/
theorem identity_eq_owner
    (C : RationalContourCategoryData)
    (X : ContourCorrespondenceObject) :
    C.identity X =
      RationalContourCombination.identity C.correspondenceLaws X :=
  C.identity_eq X

/-- Left identity reindexing supplied by rational contour category data. -/
theorem left_identity_reindexing_eq
    (C : RationalContourCategoryData)
    {X Y : ContourCorrespondenceObject}
    (F : RationalContourHom X Y) :
    RationalContourCombinationReindexing
      (C.compose (C.identity X) F) F :=
  C.left_identity_reindexing F

/-- Right identity reindexing supplied by rational contour category data. -/
theorem right_identity_reindexing_eq
    (C : RationalContourCategoryData)
    {X Y : ContourCorrespondenceObject}
    (F : RationalContourHom X Y) :
    RationalContourCombinationReindexing
      (C.compose F (C.identity Y)) F :=
  C.right_identity_reindexing F

/-- Associativity reindexing supplied by rational contour category data. -/
theorem associativity_reindexing_eq
    (C : RationalContourCategoryData)
    {W X Y Z : ContourCorrespondenceObject}
    (F : RationalContourHom W X)
    (G : RationalContourHom X Y)
    (H : RationalContourHom Y Z) :
    RationalContourCombinationReindexing
      (C.compose (C.compose F G) H)
      (C.compose F (C.compose G H)) :=
  C.associativity_reindexing F G H

/-- The rational contour category data induced by contour-correspondence law data. -/
def ofCorrespondenceLaws
    (L : ContourCorrespondenceCategoryLawData) :
    RationalContourCategoryData where
  correspondenceLaws := L
  identity := RationalContourCombination.identity L
  compose := RationalContourCombination.comp L
  identity_eq := fun _ => rfl
  left_identity_reindexing :=
    RationalContourCombinationReindexing.leftIdentity L
  right_identity_reindexing :=
    RationalContourCombinationReindexing.rightIdentity L
  associativity_reindexing :=
    RationalContourCombinationReindexing.associativity L

end RationalContourCategoryData

end AnalyticMotives
end LFunctions
end Boundary
