import Boundary.Localization
import Boundary.PresheavesWithTransfers
import Boundary.SmSchemeOverPullbacks
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq

/-!
# Nisnevich Square Targets For Presheaves With Transfers

This file records typed Nisnevich distinguished-square data together with the
chosen transfer maps that feed the proof-relevant localization scaffold. It
does not yet state a global Nisnevich descent predicate on arbitrary
presheaves with transfers.
-/

universe u

variable {k : Type u} [Field k] [PerfectField k]

open AlgebraicGeometry CategoryTheory

namespace Boundary

noncomputable section

/-- Typed Nisnevich distinguished-square data, together with chosen transfer
realizations of the four structural maps.  The geometric compatibility facts
that still need proofs are left as precisely named targets rather than being
collapsed into a single opaque proposition. -/
structure NisnevichDistinguishedSquareDataQ (category : SmCorQ (k := k)) where
  base : Geometry.SmSchemeOver k
  openPiece : Geometry.SmSchemeOver k
  patchPiece : Geometry.SmSchemeOver k
  overlap : Geometry.SmSchemeOver k
  openToBase : openPiece ⟶ base
  patchToBase : patchPiece ⟶ base
  overlapToOpen : overlap ⟶ openPiece
  overlapToPatch : overlap ⟶ patchPiece
  openToBaseTransfer : SmCorQ.Hom category openPiece base
  patchToBaseTransfer : SmCorQ.Hom category patchPiece base
  overlapToOpenTransfer : SmCorQ.Hom category overlap openPiece
  overlapToPatchTransfer : SmCorQ.Hom category overlap patchPiece
  overlap_to_base_transfer_commutes :
    category.comp overlapToOpenTransfer openToBaseTransfer =
      category.comp overlapToPatchTransfer patchToBaseTransfer
  openToBase_isOpenImmersion : IsOpenImmersion openToBase.hom
  patchToBase_isEtale : IsEtale patchToBase.hom
  overlap_isPullback : IsPullback overlapToOpen.hom overlapToPatch.hom openToBase.hom patchToBase.hom

namespace NisnevichDistinguishedSquareDataQ

def descentSource {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    PST category :=
  Qtr (category := category) square.overlap

def descentTarget {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    PST category :=
  directSum
    (Qtr (category := category) square.openPiece)
    (Qtr (category := category) square.patchPiece)

/-- On the current representable surface, the variance-correct open restriction
leg points from the overlap representable to the open-piece representable. -/
def descentOpenRestrictionMap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentSource square ⟶ Qtr (category := category) square.openPiece :=
  QtrMap (category := category) square.overlapToOpenTransfer

/-- On the current representable surface, the variance-correct patch
restriction leg points from the overlap representable to the patch-piece
representable. -/
def descentPatchRestrictionMap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentSource square ⟶ Qtr (category := category) square.patchPiece :=
  QtrMap (category := category) square.overlapToPatchTransfer

/-- The overlap-difference map into the open/patch direct-sum presentation.
Its cokernel is the closest currently available categorical compatible-pair
object on the representable/direct-sum surface. -/
def descentDifferenceMap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentSource square ⟶ descentTarget square := by
  letI := SmCorQCat category
  refine
    { app := fun X =>
        { toFun := fun value =>
            ((descentOpenRestrictionMap square).app X value,
              -((descentPatchRestrictionMap square).app X value))
          map_add' := by
            intro a b
            apply Prod.ext
            · change (descentOpenRestrictionMap square).app X (a + b) =
                (descentOpenRestrictionMap square).app X a +
                  (descentOpenRestrictionMap square).app X b
              exact ((descentOpenRestrictionMap square).app X).map_add a b
            · change -((descentPatchRestrictionMap square).app X (a + b)) =
                -((descentPatchRestrictionMap square).app X a) +
                  -((descentPatchRestrictionMap square).app X b)
              rw [((descentPatchRestrictionMap square).app X).map_add]
              abel
          map_smul' := by
            intro coeff value
            apply Prod.ext
            · change (descentOpenRestrictionMap square).app X (coeff • value) =
                coeff • (descentOpenRestrictionMap square).app X value
              exact ((descentOpenRestrictionMap square).app X).map_smul coeff value
            · change -((descentPatchRestrictionMap square).app X (coeff • value)) =
                coeff • (-((descentPatchRestrictionMap square).app X value))
              simpa using
                congrArg Neg.neg (((descentPatchRestrictionMap square).app X).map_smul coeff value) }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro value
        apply Prod.ext
        · exact DFunLike.congr_fun
            ((descentOpenRestrictionMap square).naturality f) value
        · calc
            -((descentPatchRestrictionMap square).app Y
                ((descentSource square).map f value))
              = -((Qtr (category := category) square.patchPiece).map f
                  ((descentPatchRestrictionMap square).app X value)) := by
                    exact congrArg Neg.neg <|
                      DFunLike.congr_fun
                        ((descentPatchRestrictionMap square).naturality f) value
            _ = (Qtr (category := category) square.patchPiece).map f
                  (-((descentPatchRestrictionMap square).app X value)) := by
                    simp }

/-- Exact remaining categorical obligation for the compatible-pair object on
the current representable/direct-sum surface. Because the available
representable restriction legs are variance-correct maps out of `Qtr overlap`,
the missing object is the cokernel of `descentDifferenceMap square`. -/
def descentCompatiblePairObject_obligation {category : SmCorQ (k := k)}
  (square : NisnevichDistinguishedSquareDataQ category) :=
  Limits.HasCokernel (descentDifferenceMap square)

/-- `PST category` has cokernels, inherited pointwise from `ModuleCat ℚ`
through the functor-category colimit instances. -/
theorem PST_hasCokernels
    (category : SmCorQ (k := k)) :
    Limits.HasCokernels (PST category) := by
  letI := SmCorQCat category
  change Limits.HasCokernels ((Geometry.SmSchemeOver k)ᵒᵖ ⥤ ModuleCat.{u + 1} ℚ)
  infer_instance

/-- The Nisnevich overlap-difference map has a cokernel in `PST category`. -/
theorem descentCompatiblePairObject_hasCokernel
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    Limits.HasCokernel (descentDifferenceMap square) := by
  letI : Limits.HasCokernels (PST category) := PST_hasCokernels (category := category)
  infer_instance

/-- The compatible-pair object attached to a Nisnevich square, defined as the
cokernel object of the overlap-difference map. -/
def descentCompatiblePairObject
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    PST category := by
  letI : Limits.HasCokernel (descentDifferenceMap square) :=
    descentCompatiblePairObject_hasCokernel (square := square)
  exact Limits.cokernel (descentDifferenceMap square)

/-- The canonical quotient map from open/patch data to the compatible-pair
object. -/
def descentCompatiblePairQuotientMap
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTarget square ⟶ descentCompatiblePairObject square := by
  letI : Limits.HasCokernel (descentDifferenceMap square) :=
    descentCompatiblePairObject_hasCokernel (square := square)
  exact Limits.cokernel.π (descentDifferenceMap square)

/-- The current representable open/patch comparison morphism into the base
representable for a Nisnevich distinguished square. This is the honest map
available before packaging the compatible-pair gluing object itself. -/
def descentComparisonMap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTarget square ⟶ Qtr (category := category) square.base := by
  letI := SmCorQCat category
  refine
    { app := fun X =>
        { toFun := fun value =>
            (QtrMap (category := category) square.openToBaseTransfer).app X value.1 +
              (QtrMap (category := category) square.patchToBaseTransfer).app X value.2
          map_add' := by
            rintro ⟨open₁, patch₁⟩ ⟨open₂, patch₂⟩
            change
              (QtrMap (category := category) square.openToBaseTransfer).app X (open₁ + open₂) +
                  (QtrMap (category := category) square.patchToBaseTransfer).app X
                    (patch₁ + patch₂) =
                ((QtrMap (category := category) square.openToBaseTransfer).app X open₁ +
                    (QtrMap (category := category) square.patchToBaseTransfer).app X patch₁) +
                  ((QtrMap (category := category) square.openToBaseTransfer).app X open₂ +
                    (QtrMap (category := category) square.patchToBaseTransfer).app X patch₂)
            rw [LinearMap.map_add, LinearMap.map_add]
            abel
          map_smul' := by
            rintro coeff ⟨openPart, patchPart⟩
            change
              (QtrMap (category := category) square.openToBaseTransfer).app X
                  (coeff • openPart) +
                (QtrMap (category := category) square.patchToBaseTransfer).app X
                  (coeff • patchPart) =
                coeff •
                  ((QtrMap (category := category) square.openToBaseTransfer).app X openPart +
                    (QtrMap (category := category) square.patchToBaseTransfer).app X patchPart)
            rw [LinearMap.map_smul, LinearMap.map_smul, smul_add] }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        rintro ⟨openPart, patchPart⟩
        change
          (QtrMap (category := category) square.openToBaseTransfer).app Y
              ((Qtr (category := category) square.openPiece).map f openPart) +
            (QtrMap (category := category) square.patchToBaseTransfer).app Y
              ((Qtr (category := category) square.patchPiece).map f patchPart) =
          (Qtr (category := category) square.base).map f
            ((QtrMap (category := category) square.openToBaseTransfer).app X openPart +
              (QtrMap (category := category) square.patchToBaseTransfer).app X patchPart)
        rw [LinearMap.map_add]
        congr 1
        · exact DFunLike.congr_fun
            ((QtrMap (category := category) square.openToBaseTransfer).naturality f)
            openPart
        · exact DFunLike.congr_fun
            ((QtrMap (category := category) square.patchToBaseTransfer).naturality f)
            patchPart }

/-- The overlap-difference map lands in the kernel of the descent comparison
map, by transfer-level commutativity on the distinguished square. -/
theorem descentComparisonMap_factors
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentDifferenceMap square ≫ descentComparisonMap square = 0 := by
  letI := SmCorQCat category
  ext X value
  change
    category.comp (category.comp value square.overlapToOpenTransfer) square.openToBaseTransfer +
      category.comp (-category.comp value square.overlapToPatchTransfer) square.patchToBaseTransfer = 0
  rw [show -category.comp value square.overlapToPatchTransfer =
      (-1 : ℚ) • category.comp value square.overlapToPatchTransfer by simp]
  rw [category.smul_comp, category.assoc, category.assoc]
  have hcomm := congrArg (fun t => category.comp value t) square.overlap_to_base_transfer_commutes
  have hcomm' :
      category.comp value (category.comp square.overlapToOpenTransfer square.openToBaseTransfer) =
        category.comp value (category.comp square.overlapToPatchTransfer square.patchToBaseTransfer) := by
    simpa using hcomm
  rw [hcomm']
  simpa [neg_one_smul]

/-- The Nisnevich descent generator map in the variance-correct direction:
from the compatible-pair quotient object to the base representable. -/
def nisnevichDescentGeneratorMap
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (hFactor : descentDifferenceMap square ≫ descentComparisonMap square = 0) :
    descentCompatiblePairObject square ⟶ Qtr (category := category) square.base := by
  letI : Limits.HasCokernel (descentDifferenceMap square) :=
    descentCompatiblePairObject_hasCokernel (square := square)
  exact Limits.cokernel.desc (descentDifferenceMap square) (descentComparisonMap square) hFactor

/-- Canonical Nisnevich descent generator map obtained from the proven
factorization condition. -/
def nisnevichDescentGeneratorMapCanonical
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentCompatiblePairObject square ⟶ Qtr (category := category) square.base :=
  nisnevichDescentGeneratorMap square (descentComparisonMap_factors square)

/-- The Nisnevich descent source representable is transfer-linear. -/
theorem descentSource_isTransferLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsTransferLinear (descentSource square) := by
  simpa [descentSource] using
    (Qtr_isTransferLinear (category := category) square.overlap)

/-- The Nisnevich descent target direct sum is transfer-linear. -/
theorem descentTarget_isTransferLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsTransferLinear (descentTarget square) := by
  let hOpen : IsTransferLinear (Qtr (category := category) square.openPiece) :=
    Qtr_isTransferLinear (category := category) square.openPiece
  let hPatch : IsTransferLinear (Qtr (category := category) square.patchPiece) :=
    Qtr_isTransferLinear (category := category) square.patchPiece
  constructor
  · intro X Y α β
    apply LinearMap.ext
    rintro ⟨openPart, patchPart⟩
    apply Prod.ext
    · exact congrArg (fun ψ => ψ openPart) (hOpen.1 α β)
    · exact congrArg (fun ψ => ψ patchPart) (hPatch.1 α β)
  · intro X Y coeff α
    apply LinearMap.ext
    rintro ⟨openPart, patchPart⟩
    apply Prod.ext
    · exact congrArg (fun ψ => ψ openPart) (hOpen.2 coeff α)
    · exact congrArg (fun ψ => ψ patchPart) (hPatch.2 coeff α)

/-- The Nisnevich compatible-pair cokernel object is transfer-linear. -/
theorem descentCompatiblePairObject_isTransferLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsTransferLinear (descentCompatiblePairObject square) := by
  letI := SmCorQCat category
  let f : descentSource square ⟶ descentTarget square :=
    descentDifferenceMap square
  letI : Limits.HasCokernel f :=
    descentCompatiblePairObject_hasCokernel (square := square)
  have hTarget : IsTransferLinear (descentTarget square) :=
    descentTarget_isTransferLinear (square := square)
  constructor
  · intro X Y a b
    apply LinearMap.ext
    intro x
    rcases Boundary.PST_cokernel_app_surjective (f := f) (X := Opposite.op Y) x with ⟨y, rfl⟩
    have h_add_eval :
        (descentTarget square).map (Quiver.Hom.op (a + b)) y =
          ((descentTarget square).map (Quiver.Hom.op a) +
            (descentTarget square).map (Quiver.Hom.op b)) y :=
      congrArg (fun ψ => ψ y) (hTarget.1 a b)
    calc
      (Limits.cokernel f).map (Quiver.Hom.op (a + b))
          ((Limits.cokernel.π f).app (Opposite.op Y) y)
          = (Limits.cokernel.π f).app (Opposite.op X)
              ((descentTarget square).map (Quiver.Hom.op (a + b)) y) :=
              Boundary.PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op (a + b)) y
      _ = (Limits.cokernel.π f).app (Opposite.op X)
            (((descentTarget square).map (Quiver.Hom.op a) +
              (descentTarget square).map (Quiver.Hom.op b)) y) := by
            exact congrArg ((Limits.cokernel.π f).app (Opposite.op X)) h_add_eval
      _ = (Limits.cokernel.π f).app (Opposite.op X)
            ((descentTarget square).map (Quiver.Hom.op a) y) +
          (Limits.cokernel.π f).app (Opposite.op X)
            ((descentTarget square).map (Quiver.Hom.op b) y) := by
            change
              (Limits.cokernel.π f).app (Opposite.op X)
                ((descentTarget square).map (Quiver.Hom.op a) y +
                  (descentTarget square).map (Quiver.Hom.op b) y) =
              (Limits.cokernel.π f).app (Opposite.op X)
                ((descentTarget square).map (Quiver.Hom.op a) y) +
                (Limits.cokernel.π f).app (Opposite.op X)
                  ((descentTarget square).map (Quiver.Hom.op b) y)
            rw [LinearMap.map_add]
      _ = (Limits.cokernel f).map (Quiver.Hom.op a)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) +
          (Limits.cokernel f).map (Quiver.Hom.op b)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [← Boundary.PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op a) y,
              ← Boundary.PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op b) y]
      _ = ((Limits.cokernel f).map (Quiver.Hom.op a) +
            (Limits.cokernel f).map (Quiver.Hom.op b))
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [LinearMap.add_apply]
  · intro X Y coeff a
    apply LinearMap.ext
    intro x
    rcases Boundary.PST_cokernel_app_surjective (f := f) (X := Opposite.op Y) x with ⟨y, rfl⟩
    have h_smul_eval :
        (descentTarget square).map (Quiver.Hom.op (coeff • a)) y =
          (coeff • (descentTarget square).map (Quiver.Hom.op a)) y :=
      congrArg (fun ψ => ψ y) (hTarget.2 coeff a)
    calc
      (Limits.cokernel f).map (Quiver.Hom.op (coeff • a))
          ((Limits.cokernel.π f).app (Opposite.op Y) y)
          = (Limits.cokernel.π f).app (Opposite.op X)
              ((descentTarget square).map (Quiver.Hom.op (coeff • a)) y) :=
              Boundary.PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op (coeff • a)) y
      _ = (Limits.cokernel.π f).app (Opposite.op X)
            ((coeff • (descentTarget square).map (Quiver.Hom.op a)) y) := by
            exact congrArg ((Limits.cokernel.π f).app (Opposite.op X)) h_smul_eval
      _ = coeff • (Limits.cokernel.π f).app (Opposite.op X)
            ((descentTarget square).map (Quiver.Hom.op a) y) := by
            change
              (Limits.cokernel.π f).app (Opposite.op X)
                (coeff • (descentTarget square).map (Quiver.Hom.op a) y) =
              coeff • (Limits.cokernel.π f).app (Opposite.op X)
                ((descentTarget square).map (Quiver.Hom.op a) y)
            rw [LinearMap.map_smul]
      _ = coeff • (Limits.cokernel f).map (Quiver.Hom.op a)
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [Boundary.PST_cokernel_map_π_apply (f := f) (α := Quiver.Hom.op a) y]
      _ = (coeff • (Limits.cokernel f).map (Quiver.Hom.op a))
            ((Limits.cokernel.π f).app (Opposite.op Y) y) := by
            rw [LinearMap.smul_apply]


/-- Bundled linear version of the Nisnevich compatible-pair object. -/
def descentCompatiblePairObjectLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    LinearPST category :=
  ⟨descentCompatiblePairObject square,
    descentCompatiblePairObject_isTransferLinear (square := square)⟩

/-- The canonical Nisnevich generator map, lifted to `LinearPST`. -/
def nisnevichDescentGeneratorMapLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentCompatiblePairObjectLinear square ⟶
      QtrLinear (category := category) square.base := by
  change descentCompatiblePairObject square ⟶ Qtr (category := category) square.base
  exact nisnevichDescentGeneratorMapCanonical square

/-- Inclusion of the open leg into the open/patch direct-sum target. -/
def descentTargetOpenInclusion
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    Qtr (category := category) square.openPiece ⟶ descentTarget square := by
  letI := SmCorQCat category
  refine
    { app := fun X =>
        { toFun := fun openPart => (openPart, 0)
          map_add' := by
            intro a b
            apply Prod.ext
            · change a + b = a + b
              rfl
            · change (0 : (Qtr (category := category) square.patchPiece).obj X) =
                (0 : (Qtr (category := category) square.patchPiece).obj X) +
                  (0 : (Qtr (category := category) square.patchPiece).obj X)
              simp
          map_smul' := by
            intro coeff value
            change
              (coeff • value, (0 : (Qtr (category := category) square.patchPiece).obj X)) =
                (RingHom.id ℚ) coeff •
                  (value, (0 : (Qtr (category := category) square.patchPiece).obj X))
            simpa }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro value
        apply Prod.ext
        · rfl
        · change (0 : (Qtr (category := category) square.patchPiece).obj Y) =
            (Qtr (category := category) square.patchPiece).map f
              (0 : (Qtr (category := category) square.patchPiece).obj X)
          simp }

/-- Inclusion of the patch leg into the open/patch direct-sum target. -/
def descentTargetPatchInclusion
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    Qtr (category := category) square.patchPiece ⟶ descentTarget square := by
  letI := SmCorQCat category
  refine
    { app := fun X =>
        { toFun := fun patchPart => (0, patchPart)
          map_add' := by
            intro a b
            apply Prod.ext
            · change (0 : (Qtr (category := category) square.openPiece).obj X) =
                (0 : (Qtr (category := category) square.openPiece).obj X) +
                  (0 : (Qtr (category := category) square.openPiece).obj X)
              simp
            · change a + b = a + b
              rfl
          map_smul' := by
            intro coeff value
            change
              ((0 : (Qtr (category := category) square.openPiece).obj X), coeff • value) =
                (RingHom.id ℚ) coeff •
                  ((0 : (Qtr (category := category) square.openPiece).obj X), value)
            simpa }
      naturality := by
        intro X Y f
        apply LinearMap.ext
        intro value
        apply Prod.ext
        · change (0 : (Qtr (category := category) square.openPiece).obj Y) =
            (Qtr (category := category) square.openPiece).map f
              (0 : (Qtr (category := category) square.openPiece).obj X)
          simp
        · rfl }

/-- Composing the open inclusion with the descent comparison map recovers the
open-to-base representable map. -/
theorem descentTargetOpenInclusion_comp_descentComparison
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTargetOpenInclusion square ≫ descentComparisonMap square =
      QtrMap (category := category) square.openToBaseTransfer := by
  letI := SmCorQCat category
  ext X value
  change
    (QtrMap (category := category) square.openToBaseTransfer).app X value +
      (QtrMap (category := category) square.patchToBaseTransfer).app X 0 =
        (QtrMap (category := category) square.openToBaseTransfer).app X value
  simp

/-- Composing the patch inclusion with the descent comparison map recovers the
patch-to-base representable map. -/
theorem descentTargetPatchInclusion_comp_descentComparison
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTargetPatchInclusion square ≫ descentComparisonMap square =
      QtrMap (category := category) square.patchToBaseTransfer := by
  letI := SmCorQCat category
  ext X value
  change
    (QtrMap (category := category) square.openToBaseTransfer).app X 0 +
      (QtrMap (category := category) square.patchToBaseTransfer).app X value =
        (QtrMap (category := category) square.patchToBaseTransfer).app X value
  simp

/-- The open leg of the linear descent generator agrees with the open-to-base
representable map after passing through the quotient projection. -/
theorem descentTargetOpenInclusion_comp_quotient_comp_generatorLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTargetOpenInclusion square ≫
        descentCompatiblePairQuotientMap square ≫
        nisnevichDescentGeneratorMapLinear square =
      QtrMap (category := category) square.openToBaseTransfer := by
  letI := SmCorQCat category
  let f : descentSource square ⟶ descentTarget square := descentDifferenceMap square
  have hπ :
      descentCompatiblePairQuotientMap square ≫
          nisnevichDescentGeneratorMapLinear square =
        descentComparisonMap square := by
    simpa [descentCompatiblePairQuotientMap, nisnevichDescentGeneratorMapLinear,
      nisnevichDescentGeneratorMapCanonical, nisnevichDescentGeneratorMap,
      f, Category.assoc] using
      (Limits.cokernel.π_desc f (descentComparisonMap square)
        (descentComparisonMap_factors square))
  calc
    descentTargetOpenInclusion square ≫
        descentCompatiblePairQuotientMap square ≫
        nisnevichDescentGeneratorMapLinear square
      = descentTargetOpenInclusion square ≫ descentComparisonMap square := by
          simpa [Category.assoc] using
            congrArg (fun t => descentTargetOpenInclusion square ≫ t) hπ
    _ = QtrMap (category := category) square.openToBaseTransfer :=
      descentTargetOpenInclusion_comp_descentComparison (square := square)

/-- The patch leg of the linear descent generator agrees with the patch-to-base
representable map after passing through the quotient projection. -/
theorem descentTargetPatchInclusion_comp_quotient_comp_generatorLinear
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category) :
    descentTargetPatchInclusion square ≫
        descentCompatiblePairQuotientMap square ≫
        nisnevichDescentGeneratorMapLinear square =
      QtrMap (category := category) square.patchToBaseTransfer := by
  letI := SmCorQCat category
  let f : descentSource square ⟶ descentTarget square := descentDifferenceMap square
  have hπ :
      descentCompatiblePairQuotientMap square ≫
          nisnevichDescentGeneratorMapLinear square =
        descentComparisonMap square := by
    simpa [descentCompatiblePairQuotientMap, nisnevichDescentGeneratorMapLinear,
      nisnevichDescentGeneratorMapCanonical, nisnevichDescentGeneratorMap,
      f, Category.assoc] using
      (Limits.cokernel.π_desc f (descentComparisonMap square)
        (descentComparisonMap_factors square))
  calc
    descentTargetPatchInclusion square ≫
        descentCompatiblePairQuotientMap square ≫
        nisnevichDescentGeneratorMapLinear square
      = descentTargetPatchInclusion square ≫ descentComparisonMap square := by
          simpa [Category.assoc] using
            congrArg (fun t => descentTargetPatchInclusion square ≫ t) hπ
    _ = QtrMap (category := category) square.patchToBaseTransfer :=
      descentTargetPatchInclusion_comp_descentComparison (square := square)

/-- Any section of the base representable induces compatible open/patch
sections on the overlap by commutativity of the distinguished square. -/
theorem baseSection_overlap_compatible
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {F : PST category}
    (ηbase : Qtr (category := category) square.base ⟶ F) :
    (QtrMap (category := category) square.overlapToOpenTransfer) ≫
        (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase =
      (QtrMap (category := category) square.overlapToPatchTransfer) ≫
        (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase := by
  letI := SmCorQCat category
  ext X value
  change
    ηbase.app X
        (category.comp (category.comp value square.overlapToOpenTransfer)
          square.openToBaseTransfer) =
      ηbase.app X
        (category.comp (category.comp value square.overlapToPatchTransfer)
          square.patchToBaseTransfer)
  simpa [category.assoc] using
    congrArg (fun t => ηbase.app X (category.comp value t))
      square.overlap_to_base_transfer_commutes

/-- Any morphism out of the compatible-pair object induces overlap-compatible
open/patch restrictions. -/
theorem descentCompatiblePairObject_overlap_compat
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (L : LinearPST category)
    (η : descentCompatiblePairObjectLinear square ⟶ L) :
    (QtrMap (category := category) square.overlapToOpenTransfer) ≫
        (descentTargetOpenInclusion square ≫
          descentCompatiblePairQuotientMap square ≫ η) =
      (QtrMap (category := category) square.overlapToPatchTransfer) ≫
        (descentTargetPatchInclusion square ≫
          descentCompatiblePairQuotientMap square ≫ η) := by
  letI := SmCorQCat category
  let f : descentSource square ⟶ descentTarget square := descentDifferenceMap square
  let ηP : descentCompatiblePairObject square ⟶ L.toPST := η
  let qη : descentTarget square ⟶ L.toPST := descentCompatiblePairQuotientMap square ≫ ηP
  have hfq : f ≫ descentCompatiblePairQuotientMap square = 0 := by
    simpa [descentCompatiblePairQuotientMap, f] using (Limits.cokernel.condition f)
  have hzero : f ≫ qη = 0 := by
    simpa [qη, Category.assoc] using congrArg (fun t => t ≫ ηP) hfq
  ext X value
  have hzeroX := congrArg (fun t => t.app X value) hzero
  set a : (Qtr (category := category) square.openPiece).obj X :=
    (descentOpenRestrictionMap square).app X value
  set b : (Qtr (category := category) square.patchPiece).obj X :=
    (descentPatchRestrictionMap square).app X value
  let zopen : (Qtr (category := category) square.openPiece).obj X := 0
  let zpatch : (Qtr (category := category) square.patchPiece).obj X := 0
  have hz : qη.app X (a, -b) = 0 := by
    simpa [qη, f, a, b, Category.assoc] using hzeroX
  have hsum : qη.app X (a, zpatch) + qη.app X (zopen, -b) = 0 := by
    have hpair : ((a, zpatch) + (zopen, -b)) = (a, -b) := by
      apply Prod.ext <;> simp
    calc
      qη.app X (a, zpatch) + qη.app X (zopen, -b)
          = qη.app X ((a, zpatch) + (zopen, -b)) := by
              exact ((qη.app X).map_add (a, zpatch) (zopen, -b)).symm
      _ = qη.app X (a, -b) := by
            exact congrArg (qη.app X) hpair
      _ = 0 := hz
  have hsub : qη.app X (a, zpatch) - qη.app X (zopen, b) = 0 := by
    have hneg : qη.app X (zopen, -b) = -(qη.app X (zopen, b)) := by
      have hsmulPair : (zopen, -b) = (-1 : ℚ) • (zopen, b) := by
        apply Prod.ext <;> simp [zopen]
      calc
        qη.app X (zopen, -b) = qη.app X (((-1 : ℚ) • (zopen, b))) := by
          exact congrArg (qη.app X) hsmulPair
        _ = (-1 : ℚ) • qη.app X (zopen, b) := by
          rw [LinearMap.map_smul]
        _ = -(qη.app X (zopen, b)) := by
          simp
    calc
      qη.app X (a, zpatch) - qη.app X (zopen, b)
          = qη.app X (a, zpatch) + (-(qη.app X (zopen, b))) := by
              simp [sub_eq_add_neg]
      _ = qη.app X (a, zpatch) + qη.app X (zopen, -b) := by
            simpa [hneg]
      _ = 0 := hsum
  exact sub_eq_zero.mp <| by
    simpa [a, b, zopen, zpatch, qη, ηP, Category.assoc] using hsub

/-- Pairing map from open and patch components into a local linear target. -/
def descentTargetPairingMap
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {L : LinearPST category}
    (ηU : Qtr (category := category) square.openPiece ⟶ L.toPST)
    (ηV : Qtr (category := category) square.patchPiece ⟶ L.toPST) :
    descentTarget square ⟶ L.toPST := by
  letI := SmCorQCat category
  refine
    { app := fun X =>
        { toFun := fun value => ηU.app X value.1 + ηV.app X value.2
          map_add' := by
            rintro ⟨u1, v1⟩ ⟨u2, v2⟩
            change
              ηU.app X (u1 + u2) + ηV.app X (v1 + v2) =
                (ηU.app X u1 + ηV.app X v1) + (ηU.app X u2 + ηV.app X v2)
            rw [LinearMap.map_add, LinearMap.map_add]
            abel
          map_smul' := by
            intro coeff value
            rcases value with ⟨u, v⟩
            change
              ηU.app X (coeff • u) + ηV.app X (coeff • v) =
                coeff • (ηU.app X u + ηV.app X v)
            rw [LinearMap.map_smul, LinearMap.map_smul, smul_add] }
      naturality := by
        intro X Y f
        ext value
        rcases value with ⟨u, v⟩
        change
          ηU.app Y ((Qtr (category := category) square.openPiece).map f u) +
              ηV.app Y ((Qtr (category := category) square.patchPiece).map f v) =
            (L.toPST.map f) (ηU.app X u + ηV.app X v)
        rw [LinearMap.map_add]
        congr 1
        · exact DFunLike.congr_fun (ηU.naturality f) u
        · exact DFunLike.congr_fun (ηV.naturality f) v }

/-- Compatibility of open/patch data exactly means the difference map is sent
to zero by the corresponding pairing map. -/
theorem descentDifferenceMap_comp_pairing_zero
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {L : LinearPST category}
    {ηU : Qtr (category := category) square.openPiece ⟶ L.toPST}
    {ηV : Qtr (category := category) square.patchPiece ⟶ L.toPST}
    (hcompat :
      (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηU =
        (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηV) :
    descentDifferenceMap square ≫
      descentTargetPairingMap square ηU ηV = 0 := by
  letI := SmCorQCat category
  ext X value
  have hcompatX := congrArg (fun t => t.app X value) hcompat
  change
    ηU.app X ((descentOpenRestrictionMap square).app X value) +
        ηV.app X (-((descentPatchRestrictionMap square).app X value)) = 0
  rw [LinearMap.map_neg]
  calc
    ηU.app X ((descentOpenRestrictionMap square).app X value) +
        -ηV.app X ((descentPatchRestrictionMap square).app X value)
      = ηU.app X ((descentOpenRestrictionMap square).app X value) -
          ηV.app X ((descentPatchRestrictionMap square).app X value) := by
            simp [sub_eq_add_neg]
    _ = 0 := by
          exact sub_eq_zero.mpr hcompatX

/-- Open component recovery from a pairing map. -/
theorem descentTargetOpenInclusion_pairing
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {L : LinearPST category}
    (ηU : Qtr (category := category) square.openPiece ⟶ L.toPST)
    (ηV : Qtr (category := category) square.patchPiece ⟶ L.toPST) :
    descentTargetOpenInclusion square ≫ descentTargetPairingMap square ηU ηV = ηU := by
  letI := SmCorQCat category
  ext X value
  change ηU.app X value + ηV.app X 0 = ηU.app X value
  simp

/-- Patch component recovery from a pairing map. -/
theorem descentTargetPatchInclusion_pairing
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {L : LinearPST category}
    (ηU : Qtr (category := category) square.openPiece ⟶ L.toPST)
    (ηV : Qtr (category := category) square.patchPiece ⟶ L.toPST) :
    descentTargetPatchInclusion square ≫ descentTargetPairingMap square ηU ηV = ηV := by
  letI := SmCorQCat category
  ext X value
  change ηU.app X 0 + ηV.app X value = ηV.app X value
  simp

/-- Every compatible open/patch pair descends uniquely through the Nisnevich
compatible-pair cokernel object. -/
theorem descentCompatiblePair_desc
    {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    {L : LinearPST category}
    {ηU : Qtr (category := category) square.openPiece ⟶ L.toPST}
    {ηV : Qtr (category := category) square.patchPiece ⟶ L.toPST}
    (hcompat :
      (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηU =
        (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηV) :
    ∃! η : descentCompatiblePairObjectLinear square ⟶ L,
      descentTargetOpenInclusion square ≫
          descentCompatiblePairQuotientMap square ≫ η = ηU ∧
        descentTargetPatchInclusion square ≫
          descentCompatiblePairQuotientMap square ≫ η = ηV := by
  letI := SmCorQCat category
  let f : descentSource square ⟶ descentTarget square := descentDifferenceMap square
  letI : Limits.HasCokernel f :=
    descentCompatiblePairObject_hasCokernel (square := square)
  let θ : descentTarget square ⟶ L.toPST :=
    descentTargetPairingMap square ηU ηV
  have hθ : f ≫ θ = 0 :=
    descentDifferenceMap_comp_pairing_zero (square := square) hcompat
  refine ⟨Limits.cokernel.desc f θ hθ, ?_, ?_⟩
  · constructor
    · calc
        descentTargetOpenInclusion square ≫
            descentCompatiblePairQuotientMap square ≫
            Limits.cokernel.desc f θ hθ
          = descentTargetOpenInclusion square ≫ θ := by
              simpa [descentCompatiblePairQuotientMap, f, Category.assoc] using
                congrArg (fun t => descentTargetOpenInclusion square ≫ t)
                  (Limits.cokernel.π_desc f θ hθ)
      _ = ηU := descentTargetOpenInclusion_pairing (square := square) ηU ηV
    · calc
        descentTargetPatchInclusion square ≫
            descentCompatiblePairQuotientMap square ≫
            Limits.cokernel.desc f θ hθ
          = descentTargetPatchInclusion square ≫ θ := by
              simpa [descentCompatiblePairQuotientMap, f, Category.assoc] using
                congrArg (fun t => descentTargetPatchInclusion square ≫ t)
                  (Limits.cokernel.π_desc f θ hθ)
      _ = ηV := descentTargetPatchInclusion_pairing (square := square) ηU ηV
  · intro η hη
    have hq : descentCompatiblePairQuotientMap square ≫ η = θ := by
      ext X value
      rcases value with ⟨u, v⟩
      have hηU := congrArg (fun t => t.app X u) hη.1
      have hηV := congrArg (fun t => t.app X v) hη.2
      let qX := (descentCompatiblePairQuotientMap square).app X
      have huv : (u, v) = (u, (0 : (Qtr (category := category) square.patchPiece).obj X)) +
          ((0 : (Qtr (category := category) square.openPiece).obj X), v) := by
        apply Prod.ext <;> simp
      have hq_add :
          qX (u, v) = qX (u, 0) + qX (0, v) := by
        calc
          qX (u, v) = qX ((u, 0) + (0, v)) := by
            exact congrArg qX huv
          _ = qX (u, 0) + qX (0, v) := by
                simpa using qX.map_add (u, 0) (0, v)
      change
        ((descentCompatiblePairQuotientMap square ≫ η).app X (u, v)) =
          ηU.app X u + ηV.app X v
      calc
        (descentCompatiblePairQuotientMap square ≫ η).app X (u, v)
          = η.app X ((descentCompatiblePairQuotientMap square).app X (u, v)) := by
              rfl
        _ = η.app X
          (qX (u, 0) + qX (0, v)) := by
              exact congrArg (η.app X) hq_add
        _ = (descentCompatiblePairQuotientMap square ≫ η).app X (u, 0) +
          (descentCompatiblePairQuotientMap square ≫ η).app X (0, v) := by
          change η.app X (qX (u, 0) + qX (0, v)) = η.app X (qX (u, 0)) + η.app X (qX (0, v))
          rw [LinearMap.map_add]
        _ = ηU.app X u + (descentCompatiblePairQuotientMap square ≫ η).app X (0, v) := by
              exact congrArg
                (fun z => z + (descentCompatiblePairQuotientMap square ≫ η).app X (0, v)) hηU
        _ = ηU.app X u + ηV.app X v := by
              exact congrArg (fun z => ηU.app X u + z) hηV
    haveI : Epi (descentCompatiblePairQuotientMap square) := by
      dsimp [descentCompatiblePairQuotientMap, f]
      infer_instance
    apply (CategoryTheory.cancel_epi (descentCompatiblePairQuotientMap square)).1
    calc
      descentCompatiblePairQuotientMap square ≫ η = θ := hq
      _ = descentCompatiblePairQuotientMap square ≫ Limits.cokernel.desc f θ hθ := by
        symm
        simpa [descentCompatiblePairQuotientMap, f, Category.assoc] using
          (Limits.cokernel.π_desc f θ hθ)

def baseRestrictionToOpen {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (F : PST category) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op square.openToBaseTransfer)

def baseRestrictionToPatch {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (F : PST category) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op square.patchToBaseTransfer)

def openRestrictionToOverlap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (F : PST category) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op square.overlapToOpenTransfer)

def patchRestrictionToOverlap {category : SmCorQ (k := k)}
    (square : NisnevichDistinguishedSquareDataQ category)
    (F : PST category) := by
  letI := SmCorQCat category
  exact F.map (Quiver.Hom.op square.overlapToPatchTransfer)

open Limits in
/-- Scheme-level geometric base-change stability for a Nisnevich distinguished square.

Given a square `sq` and a base-change morphism `f : SmOverHom Y sq.base`, the
pulled-back structural morphisms satisfy the three typed Nisnevich geometric conditions:

1. `pullback.snd sq.openToBase.hom f.hom` is an open immersion — by the Mathlib
   instance `IsOpenImmersion.pullback_snd_of_left`, which fires from
   `sq.openToBase_isOpenImmersion`.

2. `pullback.snd sq.patchToBase.hom f.hom` is étale — by
   `MorphismProperty.IsStableUnderBaseChange @IsEtale` (an inferrable instance)
   together with `MorphismProperty.pullback_snd`.

3. The fiber product of the two new structural morphisms is a pullback square — by
   the universal property of the scheme-level pullback via `IsPullback.of_hasPullback`.

These three typed facts are exactly `openToBase_isOpenImmersion`, `patchToBase_isEtale`,
and `overlap_isPullback` for the base-changed `NisnevichDistinguishedSquareDataQ`.
The corresponding transfer maps (the deeper blocker) are not produced here. -/
theorem pullback_geometry {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsOpenImmersion (pullback.snd sq.openToBase.hom f.hom) ∧
    IsEtale (pullback.snd sq.patchToBase.hom f.hom) ∧
    IsPullback
      (pullback.fst (pullback.snd sq.openToBase.hom f.hom)
                    (pullback.snd sq.patchToBase.hom f.hom))
      (pullback.snd (pullback.snd sq.openToBase.hom f.hom)
                    (pullback.snd sq.patchToBase.hom f.hom))
      (pullback.snd sq.openToBase.hom f.hom)
      (pullback.snd sq.patchToBase.hom f.hom) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (1) Open immersions are stable under base change.
    -- `pullback_snd_of_left` fires from `[IsOpenImmersion sq.openToBase.hom]`.
    haveI := sq.openToBase_isOpenImmersion
    infer_instance
  · -- (2) Étale morphisms are stable under base change.
    letI : MorphismProperty.IsStableUnderBaseChange @IsEtale := inferInstance
    exact MorphismProperty.pullback_snd sq.patchToBase.hom f.hom sq.patchToBase_isEtale
  · -- (3) Universal property of the scheme-level pullback.
    -- `hasPullback_of_left` fires because the left morphism is an open immersion.
    haveI := sq.openToBase_isOpenImmersion
    exact IsPullback.of_hasPullback _ _

private theorem openToBase_isSmooth {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    IsSmooth sq.openToBase.hom := by
  letI := sq.openToBase_isOpenImmersion
  infer_instance

private theorem openToBase_isSeparated {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    IsSeparated sq.openToBase.hom := by
  letI := sq.openToBase_isOpenImmersion
  infer_instance

private theorem openToBase_isFiniteType {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    Geometry.IsOfFiniteType sq.openToBase.hom := by
  letI := sq.openToBase_isOpenImmersion
  exact ⟨inferInstance, inferInstance⟩

private theorem patchToBase_isSmooth {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    IsSmooth sq.patchToBase.hom := by
  exact sq.patchToBase_isEtale.isSmooth

private theorem patchToBase_isSeparated {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    IsSeparated sq.patchToBase.hom := by
  letI : IsSeparated sq.base.structMap := sq.base.separated
  letI : IsSeparated (sq.patchToBase.hom ≫ sq.base.structMap) := by
    simpa [sq.patchToBase.over] using sq.patchPiece.separated
  exact IsSeparated.of_comp (f := sq.patchToBase.hom) (g := sq.base.structMap)

private theorem patchToBase_isFiniteType {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category) :
    Geometry.IsOfFiniteType sq.patchToBase.hom := by
  letI : LocallyOfFiniteType (sq.patchToBase.hom ≫ sq.base.structMap) := by
    simpa [sq.patchToBase.over] using sq.patchPiece.locallyOfFiniteType_structMap
  exact ⟨inferInstance,
    locallyOfFiniteType_of_comp (f := sq.patchToBase.hom) (g := sq.base.structMap)⟩

/-- The base-changed open piece `U ×_X Y`. -/
def baseChange_open {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    Geometry.SmSchemeOver k :=
  SmSchemeOver.pullbackObject
    sq.openToBase
    f
    (openToBase_isSmooth sq)
    (openToBase_isSeparated sq)
    (openToBase_isFiniteType sq)

/-- The base-changed patch piece `V ×_X Y`. -/
def baseChange_patch {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    Geometry.SmSchemeOver k :=
  SmSchemeOver.pullbackObject
    sq.patchToBase
    f
    (patchToBase_isSmooth sq)
    (patchToBase_isSeparated sq)
    (patchToBase_isFiniteType sq)

/-- The pulled-back open-to-base structural morphism `U ×_X Y ⟶ Y`. -/
def baseChange_open_to_base {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    SmOverHom (baseChange_open sq f) Y :=
  SmSchemeOver.pullbackSnd
    sq.openToBase
    f
    (openToBase_isSmooth sq)
    (openToBase_isSeparated sq)
    (openToBase_isFiniteType sq)

/-- The pulled-back patch-to-base structural morphism `V ×_X Y ⟶ Y`. -/
def baseChange_patch_to_base {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    SmOverHom (baseChange_patch sq f) Y :=
  SmSchemeOver.pullbackSnd
    sq.patchToBase
    f
    (patchToBase_isSmooth sq)
    (patchToBase_isSeparated sq)
    (patchToBase_isFiniteType sq)

theorem baseChange_open_to_base_isOpenImmersion {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsOpenImmersion (baseChange_open_to_base sq f).hom := by
  simpa [baseChange_open_to_base, baseChange_open] using
    (pullback_geometry sq f).1

theorem baseChange_patch_to_base_isEtale {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsEtale (baseChange_patch_to_base sq f).hom := by
  simpa [baseChange_patch_to_base, baseChange_patch] using
    (pullback_geometry sq f).2.1

private theorem baseChange_open_to_base_isSmooth {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsSmooth (baseChange_open_to_base sq f).hom := by
  letI := baseChange_open_to_base_isOpenImmersion sq f
  infer_instance

private theorem baseChange_open_to_base_isSeparated {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsSeparated (baseChange_open_to_base sq f).hom := by
  letI := baseChange_open_to_base_isOpenImmersion sq f
  infer_instance

private theorem baseChange_open_to_base_isFiniteType {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    Geometry.IsOfFiniteType (baseChange_open_to_base sq f).hom := by
  letI := baseChange_open_to_base_isOpenImmersion sq f
  exact ⟨inferInstance, inferInstance⟩

/-- The pulled-back overlap `(U ×_X Y) ×_Y (V ×_X Y)`. -/
def baseChange_overlap {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    Geometry.SmSchemeOver k :=
  SmSchemeOver.pullbackObject
    (baseChange_open_to_base sq f)
    (baseChange_patch_to_base sq f)
    (baseChange_open_to_base_isSmooth sq f)
    (baseChange_open_to_base_isSeparated sq f)
    (baseChange_open_to_base_isFiniteType sq f)

/-- The overlap-to-open morphism in the pulled-back Nisnevich square. -/
def baseChange_overlap_to_open {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    SmOverHom (baseChange_overlap sq f) (baseChange_open sq f) :=
  SmSchemeOver.pullbackFst
    (baseChange_open_to_base sq f)
    (baseChange_patch_to_base sq f)
    (baseChange_open_to_base_isSmooth sq f)
    (baseChange_open_to_base_isSeparated sq f)
    (baseChange_open_to_base_isFiniteType sq f)

/-- The overlap-to-patch morphism in the pulled-back Nisnevich square. -/
def baseChange_overlap_to_patch {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    SmOverHom (baseChange_overlap sq f) (baseChange_patch sq f) :=
  SmSchemeOver.pullbackSnd
    (baseChange_open_to_base sq f)
    (baseChange_patch_to_base sq f)
    (baseChange_open_to_base_isSmooth sq f)
    (baseChange_open_to_base_isSeparated sq f)
    (baseChange_open_to_base_isFiniteType sq f)

theorem baseChange_overlap_isPullback {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    IsPullback
      (baseChange_overlap_to_open sq f).hom
      (baseChange_overlap_to_patch sq f).hom
      (baseChange_open_to_base sq f).hom
      (baseChange_patch_to_base sq f).hom := by
  simpa [baseChange_overlap_to_open, baseChange_overlap_to_patch,
    baseChange_open_to_base, baseChange_patch_to_base,
    baseChange_overlap, baseChange_open, baseChange_patch] using
    (pullback_geometry sq f).2.2

theorem baseChange_overlap_comp_eq {category : SmCorQ (k := k)}
    (sq : NisnevichDistinguishedSquareDataQ category)
    {Y : Geometry.SmSchemeOver k}
    (f : SmOverHom Y sq.base) :
    SmOverHom.comp (baseChange_overlap_to_open sq f) (baseChange_open_to_base sq f) =
      SmOverHom.comp (baseChange_overlap_to_patch sq f) (baseChange_patch_to_base sq f) :=
  SmSchemeOver.pullbackFst_comp_eq
    (baseChange_open_to_base sq f)
    (baseChange_patch_to_base sq f)
    (baseChange_open_to_base_isSmooth sq f)
    (baseChange_open_to_base_isSeparated sq f)
    (baseChange_open_to_base_isFiniteType sq f)

end NisnevichDistinguishedSquareDataQ

/-- Honest Nisnevich descent condition for one distinguished square: compatible
sections on the open and the etale patch glue uniquely to a section on the
base. -/
def IsNisnevichLocalAtSquareQ {category : SmCorQ (k := k)}
    (F : PST category) (square : NisnevichDistinguishedSquareDataQ category) := by
  letI := SmCorQCat category
  exact
    ∀ (openSection : F.obj (Opposite.op square.openPiece))
      (patchSection : F.obj (Opposite.op square.patchPiece)),
      NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F openSection =
        NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F patchSection →
        ∃! baseSection : F.obj (Opposite.op square.base),
          NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F baseSection =
              openSection ∧
            NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F baseSection =
              patchSection

/-- Honest global Nisnevich locality predicate over canonical presheaves with
transfers: every typed distinguished square in the Boundary layer satisfies the
usual unique-gluing descent condition on values of `F`. -/
def IsNisnevichLocal {category : SmCorQ (k := k)}
    (F : PST category) :=
  ∀ square : NisnevichDistinguishedSquareDataQ category,
    IsNisnevichLocalAtSquareQ F square

namespace IsNisnevichLocal

/-- Every Nisnevich-local presheaf with transfers satisfies the value-level
descent condition for each typed distinguished square. -/
theorem inverts_or_satisfies_descent_square
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : IsNisnevichLocal F)
    (square : NisnevichDistinguishedSquareDataQ category) :
    IsNisnevichLocalAtSquareQ F square :=
  hF square

/-- If a presheaf with transfers satisfies the value-level descent condition
for every typed distinguished square, then it is Nisnevich-local. -/
theorem of_satisfies_descent_square
    {category : SmCorQ (k := k)} {F : PST category}
    (hF : ∀ square : NisnevichDistinguishedSquareDataQ category,
      IsNisnevichLocalAtSquareQ F square) :
    IsNisnevichLocal F :=
  hF

/-- A presheaf with transfers is Nisnevich-local exactly when it satisfies the
value-level descent condition for every typed distinguished square. -/
theorem iff_satisfies_descent_square
    {category : SmCorQ (k := k)} {F : PST category} :
    IsNisnevichLocal F ↔
      ∀ square : NisnevichDistinguishedSquareDataQ category,
        IsNisnevichLocalAtSquareQ F square := by
  constructor
  · exact inverts_or_satisfies_descent_square
  · exact of_satisfies_descent_square

end IsNisnevichLocal

/-- For a bundled linear presheaf with transfers, Nisnevich locality is
equivalent to unique gluing for the current Yoneda-carried morphism sets out of
representables attached to a distinguished square. -/
theorem IsNisnevichLocal_iff_QtrLinear_satisfies_descent
    {category : SmCorQ (k := k)}
    (F : LinearPST category) :
    IsNisnevichLocal F.toPST ↔
      ∀ square : NisnevichDistinguishedSquareDataQ category,
        ∀ (ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ F.toPST)
          (ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ F.toPST),
          (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch →
          ∃! ηbase : (QtrLinear (category := category) square.base).toPST ⟶ F.toPST,
            (QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase = ηopen ∧
              (QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase = ηpatch := by
  letI := SmCorQCat category
  constructor
  · intro hF square ηopen ηpatch hcompat
    let openSection := QtrLinear_yoneda F square.openPiece ηopen
    let patchSection := QtrLinear_yoneda F square.patchPiece ηpatch
    have hoverlap :
        NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F.toPST
            openSection =
          NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F.toPST
            patchSection := by
      calc
        NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F.toPST
            openSection
          = QtrLinear_yoneda F square.overlap
              ((QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen) := by
              symm
              simpa [openSection,
                NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap] using
                QtrLinear_yoneda_naturality (F := F)
                  (α := square.overlapToOpenTransfer) ηopen
        _ = QtrLinear_yoneda F square.overlap
              ((QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch) := by
              simpa using congrArg (QtrLinear_yoneda F square.overlap) hcompat
        _ = NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F.toPST
              patchSection := by
              simpa [patchSection,
                NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap] using
                QtrLinear_yoneda_naturality (F := F)
                  (α := square.overlapToPatchTransfer) ηpatch
    have hsquare :=
      (IsNisnevichLocal.iff_satisfies_descent_square (F := F.toPST)).mp hF square
    rcases hsquare openSection patchSection hoverlap with ⟨baseSection, hbase, huniq⟩
    refine ⟨(QtrLinear_yoneda F square.base).invFun baseSection, ?_, ?_⟩
    · constructor
      · apply (QtrLinear_yoneda F square.openPiece).injective
        calc
          QtrLinear_yoneda F square.openPiece
              ((QtrMap (category := category) square.openToBaseTransfer) ≫
                (QtrLinear_yoneda F square.base).invFun baseSection)
            = NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                (QtrLinear_yoneda F square.base
                  ((QtrLinear_yoneda F square.base).invFun baseSection)) := by
                simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen] using
                  QtrLinear_yoneda_naturality (F := F)
                    (α := square.openToBaseTransfer)
                    ((QtrLinear_yoneda F square.base).invFun baseSection)
          _ = NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                baseSection := by
                exact congrArg
                  (NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST)
                  ((QtrLinear_yoneda F square.base).right_inv baseSection)
          _ = openSection := hbase.1
          _ = QtrLinear_yoneda F square.openPiece ηopen := by
                rfl
      · apply (QtrLinear_yoneda F square.patchPiece).injective
        calc
          QtrLinear_yoneda F square.patchPiece
              ((QtrMap (category := category) square.patchToBaseTransfer) ≫
                (QtrLinear_yoneda F square.base).invFun baseSection)
            = NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                (QtrLinear_yoneda F square.base
                  ((QtrLinear_yoneda F square.base).invFun baseSection)) := by
                simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch] using
                  QtrLinear_yoneda_naturality (F := F)
                    (α := square.patchToBaseTransfer)
                    ((QtrLinear_yoneda F square.base).invFun baseSection)
          _ = NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                baseSection := by
                exact congrArg
                  (NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST)
                  ((QtrLinear_yoneda F square.base).right_inv baseSection)
          _ = patchSection := hbase.2
          _ = QtrLinear_yoneda F square.patchPiece ηpatch := by
                rfl
    · intro ζ hζ
      apply (QtrLinear_yoneda F square.base).injective
      calc
        QtrLinear_yoneda F square.base ζ = baseSection := by
          apply huniq
          constructor
          · calc
              NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                  (QtrLinear_yoneda F square.base ζ)
                = QtrLinear_yoneda F square.openPiece
                    ((QtrMap (category := category) square.openToBaseTransfer) ≫ ζ) := by
                    symm
                    simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen] using
                      QtrLinear_yoneda_naturality (F := F)
                        (α := square.openToBaseTransfer) ζ
              _ = QtrLinear_yoneda F square.openPiece ηopen := by
                    simpa using congrArg (QtrLinear_yoneda F square.openPiece) hζ.1
              _ = openSection := by
                    rfl
          · calc
              NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                  (QtrLinear_yoneda F square.base ζ)
                = QtrLinear_yoneda F square.patchPiece
                    ((QtrMap (category := category) square.patchToBaseTransfer) ≫ ζ) := by
                    symm
                    simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch] using
                      QtrLinear_yoneda_naturality (F := F)
                        (α := square.patchToBaseTransfer) ζ
              _ = QtrLinear_yoneda F square.patchPiece ηpatch := by
                    simpa using congrArg (QtrLinear_yoneda F square.patchPiece) hζ.2
              _ = patchSection := by
                    rfl
        _ = QtrLinear_yoneda F square.base
              ((QtrLinear_yoneda F square.base).invFun baseSection) := by
              symm
              exact (QtrLinear_yoneda F square.base).right_inv baseSection
  · intro hF
    exact (IsNisnevichLocal.iff_satisfies_descent_square (F := F.toPST)).2 <| by
      intro square openSection patchSection hoverlap
      let ηopen : (QtrLinear (category := category) square.openPiece).toPST ⟶ F.toPST :=
        (QtrLinear_yoneda F square.openPiece).invFun openSection
      let ηpatch : (QtrLinear (category := category) square.patchPiece).toPST ⟶ F.toPST :=
        (QtrLinear_yoneda F square.patchPiece).invFun patchSection
      have hcompat :
          (QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen =
            (QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch := by
        apply (QtrLinear_yoneda F square.overlap).injective
        calc
          QtrLinear_yoneda F square.overlap
              ((QtrMap (category := category) square.overlapToOpenTransfer) ≫ ηopen)
            = NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F.toPST
                (QtrLinear_yoneda F square.openPiece ηopen) := by
                simpa [NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap] using
                  QtrLinear_yoneda_naturality (F := F)
                    (α := square.overlapToOpenTransfer) ηopen
          _ = NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F.toPST
                openSection := by
                exact congrArg
                  (NisnevichDistinguishedSquareDataQ.openRestrictionToOverlap square F.toPST)
                  (by simpa [ηopen] using
                    (QtrLinear_yoneda F square.openPiece).right_inv openSection)
          _ = NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F.toPST
                patchSection := hoverlap
          _ = NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F.toPST
                (QtrLinear_yoneda F square.patchPiece ηpatch) := by
                exact congrArg
                  (NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap square F.toPST)
                  (by simpa [ηpatch] using
                    ((QtrLinear_yoneda F square.patchPiece).right_inv patchSection).symm)
          _ = QtrLinear_yoneda F square.overlap
              ((QtrMap (category := category) square.overlapToPatchTransfer) ≫ ηpatch) := by
                symm
                simpa [NisnevichDistinguishedSquareDataQ.patchRestrictionToOverlap] using
                  QtrLinear_yoneda_naturality (F := F)
                    (α := square.overlapToPatchTransfer) ηpatch
      rcases hF square ηopen ηpatch hcompat with ⟨ηbase, hbase, huniq⟩
      refine ⟨QtrLinear_yoneda F square.base ηbase, ?_, ?_⟩
      · constructor
        · calc
            NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                (QtrLinear_yoneda F square.base ηbase)
              = QtrLinear_yoneda F square.openPiece
                  ((QtrMap (category := category) square.openToBaseTransfer) ≫ ηbase) := by
                  symm
                  simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen] using
                    QtrLinear_yoneda_naturality (F := F)
                      (α := square.openToBaseTransfer) ηbase
          _ = QtrLinear_yoneda F square.openPiece ηopen := by
                simpa using congrArg (QtrLinear_yoneda F square.openPiece) hbase.1
          _ = openSection := by
                simpa [ηopen] using
                  (QtrLinear_yoneda F square.openPiece).right_inv openSection
        · calc
            NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                (QtrLinear_yoneda F square.base ηbase)
              = QtrLinear_yoneda F square.patchPiece
                  ((QtrMap (category := category) square.patchToBaseTransfer) ≫ ηbase) := by
                  symm
                  simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch] using
                    QtrLinear_yoneda_naturality (F := F)
                      (α := square.patchToBaseTransfer) ηbase
          _ = QtrLinear_yoneda F square.patchPiece ηpatch := by
                simpa using congrArg (QtrLinear_yoneda F square.patchPiece) hbase.2
          _ = patchSection := by
                simpa [ηpatch] using
                  (QtrLinear_yoneda F square.patchPiece).right_inv patchSection
      · intro baseSection hbaseSection
        let ζ : (QtrLinear (category := category) square.base).toPST ⟶ F.toPST :=
          (QtrLinear_yoneda F square.base).invFun baseSection
        have hζ :
            (QtrMap (category := category) square.openToBaseTransfer) ≫ ζ = ηopen ∧
              (QtrMap (category := category) square.patchToBaseTransfer) ≫ ζ = ηpatch := by
          constructor
          · apply (QtrLinear_yoneda F square.openPiece).injective
            calc
              QtrLinear_yoneda F square.openPiece
                  ((QtrMap (category := category) square.openToBaseTransfer) ≫ ζ)
                = NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                    (QtrLinear_yoneda F square.base ζ) := by
                    simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen] using
                      QtrLinear_yoneda_naturality (F := F)
                        (α := square.openToBaseTransfer) ζ
              _ = NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST
                    baseSection := by
                    exact congrArg
                      (NisnevichDistinguishedSquareDataQ.baseRestrictionToOpen square F.toPST)
                      ((QtrLinear_yoneda F square.base).right_inv baseSection)
              _ = openSection := hbaseSection.1
              _ = QtrLinear_yoneda F square.openPiece ηopen := by
                    symm
                    simpa [ηopen] using
                      (QtrLinear_yoneda F square.openPiece).right_inv openSection
          · apply (QtrLinear_yoneda F square.patchPiece).injective
            calc
              QtrLinear_yoneda F square.patchPiece
                  ((QtrMap (category := category) square.patchToBaseTransfer) ≫ ζ)
                = NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                    (QtrLinear_yoneda F square.base ζ) := by
                    simpa [NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch] using
                      QtrLinear_yoneda_naturality (F := F)
                        (α := square.patchToBaseTransfer) ζ
              _ = NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST
                    baseSection := by
                    exact congrArg
                      (NisnevichDistinguishedSquareDataQ.baseRestrictionToPatch square F.toPST)
                      ((QtrLinear_yoneda F square.base).right_inv baseSection)
              _ = patchSection := hbaseSection.2
              _ = QtrLinear_yoneda F square.patchPiece ηpatch := by
                    symm
                    simpa [ηpatch] using
                      (QtrLinear_yoneda F square.patchPiece).right_inv patchSection
        have hzeta : ζ = ηbase := huniq ζ hζ
        calc
          baseSection = QtrLinear_yoneda F square.base ζ := by
            symm
            simpa [ζ] using (QtrLinear_yoneda F square.base).right_inv baseSection
          _ = QtrLinear_yoneda F square.base ηbase := by
            exact congrArg (QtrLinear_yoneda F square.base) hzeta

/-- Bundled Nisnevich-local presheaves with transfers.  This is a bundled
subtype of the canonical `PST` category, not a localization. -/
def NisnevichLocalPST (category : SmCorQ (k := k)) :=
  { F : PST category // IsNisnevichLocal F }

/-- Family of Nisnevich localizing maps feeding the transfer-presheaf
localization construction. -/
structure NisnevichLocalizingMapObligationQ (category : SmCorQ (k := k)) where
  Square : Type (u + 1)
  square : Square → NisnevichDistinguishedSquareDataQ category
  localizingData : Square → Sigma fun X : PST category =>
    Sigma fun Y : PST category =>
      (X ⟶ Y)

namespace NisnevichLocalizingMapObligationQ

def toLocalizingMorphisms {category : SmCorQ (k := k)}
    (presentation : NisnevichLocalizingMapObligationQ category) :
    LocalizingMorphismPresentationQ category :=
  { Generator := presentation.Square
    data := presentation.localizingData }

end NisnevichLocalizingMapObligationQ

end

end Boundary
