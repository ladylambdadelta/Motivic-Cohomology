import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Int.Defs
import Mathlib.Tactic

/-!
# Formal Tate Stabilization Interface

This file provides the small formal interface consumed by the Boundary
geometric-motives construction. The motivic input is supplied elsewhere in the
Boundary stack: effective motives, the projective-line Tate object, and the
formal operation of adjoining Tate degrees.

The object-level formal stabilization records an effective object together
with an integer Tate degree. This interface is deliberately lightweight; the
Boundary `DMgm` consumer file exposes the canonical Voevodsky construction
assembled from the effective and Tate data.
-/

universe u v

open CategoryTheory

namespace Boundary.Motives

/-- Object of the formal Tate stabilization of an effective category. -/
structure FormalTateStabilizedObject (C : Type u) where
  effectiveObj : C
  tateTwist : Int

/-- Tate-stabilized object type for a chosen Tate object. -/
abbrev StabilizedObject
    {C : Type u} [Category.{v} C]
    (_tateObject : C) :=
  FormalTateStabilizedObject C

/-- The lightweight category structure used by the Boundary construction
surface. Morphisms are inherited from the effective object component; the
Tate-degree bookkeeping is object-level data. -/
instance stabilizedObjectCategory
    {C : Type u} [Category.{v} C]
    (tateObject : C) : Category (StabilizedObject tateObject) where
  Hom X Y := X.effectiveObj ⟶ Y.effectiveObj
  id X := 𝟙 X.effectiveObj
  comp f g := f ≫ g
  id_comp := by
    intro X Y f
    simp
  comp_id := by
    intro X Y f
    simp
  assoc := by
    intro W X Y Z f g h
    simp [Category.assoc]

/-- Formal Tate stabilization of an effective category at a Tate object. -/
abbrev DMgmQ_Q
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateObject : DMgmEffQ_Q) :=
  StabilizedObject tateObject

/-- Directly named Tate stabilization of an effective category. -/
abbrev TateStabilization
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateObject : DMgmEffQ_Q) :=
  DMgmQ_Q DMgmEffQ_Q tateObject

/-- Alias emphasizing that `DMgm` is obtained from the effective layer by
Tate stabilization. -/
abbrev DMgmFromEffective
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateObject : DMgmEffQ_Q) :=
  TateStabilization DMgmEffQ_Q tateObject

/-- Embed effective objects as Tate-degree-zero stabilized objects. -/
def effectiveEmbedding
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    C ⥤ DMgmQ_Q C tateObject where
  obj X := ⟨X, 0⟩
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem effectiveEmbedding_obj_effectiveObj
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : C) :
    ((effectiveEmbedding tateObject).obj X).effectiveObj = X :=
  rfl

@[simp] theorem effectiveEmbedding_obj_tateTwist
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : C) :
    ((effectiveEmbedding tateObject).obj X).tateTwist = 0 :=
  rfl

@[simp] theorem effectiveEmbedding_map
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    {X Y : C}
    (f : X ⟶ Y) :
    (effectiveEmbedding tateObject).map f = f :=
  rfl

/-- Tate shift on stabilized objects. -/
def tateShiftObject
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    FormalTateStabilizedObject C :=
  ⟨X.effectiveObj, X.tateTwist + 1⟩

/-- Inverse Tate shift on stabilized objects. -/
def inverseTateShiftObject
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    FormalTateStabilizedObject C :=
  ⟨X.effectiveObj, X.tateTwist - 1⟩

@[simp] theorem tateShiftObject_effectiveObj
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    (tateShiftObject X).effectiveObj = X.effectiveObj :=
  rfl

@[simp] theorem tateShiftObject_tateTwist
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    (tateShiftObject X).tateTwist = X.tateTwist + 1 :=
  rfl

@[simp] theorem inverseTateShiftObject_effectiveObj
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    (inverseTateShiftObject X).effectiveObj = X.effectiveObj :=
  rfl

@[simp] theorem inverseTateShiftObject_tateTwist
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    (inverseTateShiftObject X).tateTwist = X.tateTwist - 1 :=
  rfl

@[simp] theorem inverseTateShiftObject_tateShiftObject
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    inverseTateShiftObject (tateShiftObject X) = X := by
  cases X
  simp [inverseTateShiftObject, tateShiftObject, Int.add_sub_cancel]

@[simp] theorem tateShiftObject_inverseTateShiftObject
    {C : Type u}
    (X : FormalTateStabilizedObject C) :
    tateShiftObject (inverseTateShiftObject X) = X := by
  cases X
  simp [inverseTateShiftObject, tateShiftObject, Int.sub_add_cancel]

/-- Tate shift functor on the formal stabilization. -/
def tateShift
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    DMgmQ_Q C tateObject ⥤ DMgmQ_Q C tateObject where
  obj := tateShiftObject
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem tateShift_obj_effectiveObj
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    ((tateShift tateObject).obj X).effectiveObj = X.effectiveObj :=
  rfl

@[simp] theorem tateShift_obj_tateTwist
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    ((tateShift tateObject).obj X).tateTwist = X.tateTwist + 1 :=
  rfl

@[simp] theorem tateShift_obj_effectiveEmbedding
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : C) :
    (tateShift tateObject).obj ((effectiveEmbedding tateObject).obj X) = ⟨X, 1⟩ :=
  rfl

@[simp] theorem tateShift_map
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    {X Y : DMgmQ_Q C tateObject}
    (f : X ⟶ Y) :
    (tateShift tateObject).map f = f :=
  rfl

/-- Inverse Tate shift functor on the formal stabilization. -/
def inverseTateShift
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    DMgmQ_Q C tateObject ⥤ DMgmQ_Q C tateObject where
  obj := inverseTateShiftObject
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

@[simp] theorem inverseTateShift_obj_effectiveObj
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    ((inverseTateShift tateObject).obj X).effectiveObj = X.effectiveObj :=
  rfl

@[simp] theorem inverseTateShift_obj_tateTwist
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    ((inverseTateShift tateObject).obj X).tateTwist = X.tateTwist - 1 :=
  rfl

@[simp] theorem inverseTateShift_obj_effectiveEmbedding
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : C) :
    (inverseTateShift tateObject).obj ((effectiveEmbedding tateObject).obj X) = ⟨X, -1⟩ :=
  rfl

@[simp] theorem inverseTateShift_map
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    {X Y : DMgmQ_Q C tateObject}
    (f : X ⟶ Y) :
    (inverseTateShift tateObject).map f = f :=
  rfl

@[simp] theorem inverseTateShift_obj_tateShift_obj
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    (inverseTateShift tateObject).obj ((tateShift tateObject).obj X) = X :=
  inverseTateShiftObject_tateShiftObject X

@[simp] theorem tateShift_obj_inverseTateShift_obj
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (X : DMgmQ_Q C tateObject) :
    (tateShift tateObject).obj ((inverseTateShift tateObject).obj X) = X :=
  tateShiftObject_inverseTateShiftObject X

/-- Data for a functor out of the formal Tate stabilization. Since morphisms in
the lightweight Boundary stabilization are inherited from the effective
component, such a functor is determined by its object assignment on effective
objects in every integer Tate degree, together with functoriality in the
effective component. -/
structure TateStabilizationExtension
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (D : Type u) [Category.{v} D] where
  obj : C → Int → D
  map : ∀ {X Y : C}, (X ⟶ Y) → ∀ sourceDegree targetDegree : Int,
    obj X sourceDegree ⟶ obj Y targetDegree
  map_id : ∀ (X : C) (n : Int), map (𝟙 X) n n = 𝟙 (obj X n)
  map_comp :
    ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
      (sourceDegree middleDegree targetDegree : Int),
      map (f ≫ g) sourceDegree targetDegree =
        map f sourceDegree middleDegree ≫ map g middleDegree targetDegree

namespace TateStabilizationExtension

/-- The functor out of the formal stabilization induced by degree-indexed
effective functorial data. -/
def lift
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D) :
    DMgmQ_Q C tateObject ⥤ D where
  obj X := extension.obj X.effectiveObj X.tateTwist
  map {X Y} f := extension.map f X.tateTwist Y.tateTwist
  map_id X := extension.map_id X.effectiveObj X.tateTwist
  map_comp {X Y Z} f g := by
    exact extension.map_comp f g X.tateTwist Y.tateTwist Z.tateTwist

@[simp] theorem lift_obj
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    (X : DMgmQ_Q C tateObject) :
    (extension.lift).obj X = extension.obj X.effectiveObj X.tateTwist :=
  rfl

@[simp] theorem lift_map
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    {X Y : DMgmQ_Q C tateObject}
    (f : X ⟶ Y) :
    (extension.lift).map f = extension.map f X.tateTwist Y.tateTwist :=
  rfl

/-- Restricting the lifted functor to degree zero recovers the degree-zero
effective component. -/
@[simp] theorem lift_comp_effectiveEmbedding_obj
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    (X : C) :
    ((effectiveEmbedding tateObject) ⋙ extension.lift).obj X = extension.obj X 0 :=
  rfl

/-- Restricting the lifted functor to degree zero sends maps by the degree-zero
effective component. -/
@[simp] theorem lift_comp_effectiveEmbedding_map
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    {X Y : C}
    (f : X ⟶ Y) :
    ((effectiveEmbedding tateObject) ⋙ extension.lift).map f = extension.map f 0 0 :=
  rfl

/-- The formal Tate shift raises the integer degree seen by a lifted functor. -/
@[simp] theorem lift_tateShift_obj
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    (X : DMgmQ_Q C tateObject) :
    (extension.lift.obj ((tateShift tateObject).obj X)) =
      extension.obj X.effectiveObj (X.tateTwist + 1) :=
  rfl

/-- The inverse formal Tate shift lowers the integer degree seen by a lifted
functor. -/
@[simp] theorem lift_inverseTateShift_obj
    {C : Type u} [Category.{v} C]
    {tateObject : C}
    {D : Type u} [Category.{v} D]
    (extension : TateStabilizationExtension tateObject D)
    (X : DMgmQ_Q C tateObject) :
    (extension.lift.obj ((inverseTateShift tateObject).obj X)) =
      extension.obj X.effectiveObj (X.tateTwist - 1) :=
  rfl

end TateStabilizationExtension

/-- Formal universal property of the Boundary Tate stabilization: functors out
of the stabilization are obtained by giving functorial effective data in every
integer Tate degree; degree zero is the effective embedding, and the Tate shift
is the integer-degree successor equivalence. -/
def tateStabilizationUniversalProperty
    {C : Type u} [Category.{v} C]
    (tateObject : C)
    (D : Type u) [Category.{v} D] :=
  TateStabilizationExtension tateObject D

/-- The formal Tate shift is an equivalence. -/
def tateShiftEquivalence
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    DMgmQ_Q C tateObject ≌ DMgmQ_Q C tateObject where
  functor := tateShift tateObject
  inverse := inverseTateShift tateObject
  unitIso := NatIso.ofComponents
    (fun X =>
      { hom := 𝟙 X.effectiveObj
        inv := 𝟙 X.effectiveObj
        hom_inv_id := by
          change 𝟙 X.effectiveObj ≫ 𝟙 X.effectiveObj = 𝟙 X.effectiveObj
          simp
        inv_hom_id := by
          change 𝟙 X.effectiveObj ≫ 𝟙 X.effectiveObj = 𝟙 X.effectiveObj
          simp })
    (by
      intro X Y f
      exact (Category.comp_id f).trans (Category.id_comp f).symm)
  counitIso := NatIso.ofComponents
    (fun X =>
      { hom := 𝟙 X.effectiveObj
        inv := 𝟙 X.effectiveObj
        hom_inv_id := by
          change 𝟙 X.effectiveObj ≫ 𝟙 X.effectiveObj = 𝟙 X.effectiveObj
          simp
        inv_hom_id := by
          change 𝟙 X.effectiveObj ≫ 𝟙 X.effectiveObj = 𝟙 X.effectiveObj
          simp })
    (by
      intro X Y f
      exact (Category.comp_id f).trans (Category.id_comp f).symm)
  functor_unitIso_comp := by
    intro X
    change 𝟙 X.effectiveObj ≫ 𝟙 X.effectiveObj = 𝟙 X.effectiveObj
    simp

/-- In the formal stabilization, the chosen Tate object is inverted by
degree bookkeeping: shifting the embedded Tate object down by one produces the
same effective object in Tate degree `-1`. This is the precise owner-level
fact available before any tensor identification theorem is proved downstream. -/
@[simp] theorem inverseTateShift_obj_effectiveEmbedding_tateObject
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    (inverseTateShift tateObject).obj ((effectiveEmbedding tateObject).obj tateObject) =
      ⟨tateObject, -1⟩ :=
  rfl

/-- Dually, shifting the embedded Tate object up by one produces the same
effective object in Tate degree `1`. This is the formal successor object that
becomes tensoring by Tate only after the effective tensor product is descended
and identified downstream. -/
@[simp] theorem tateShift_obj_effectiveEmbedding_tateObject
    {C : Type u} [Category.{v} C]
    (tateObject : C) :
    (tateShift tateObject).obj ((effectiveEmbedding tateObject).obj tateObject) =
      ⟨tateObject, 1⟩ :=
  rfl

end Boundary.Motives
