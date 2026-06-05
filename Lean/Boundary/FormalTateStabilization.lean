import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Int.Defs
import Mathlib.Tactic

/-!
# Formal Tate Stabilization Interface

This file provides the small formal interface consumed by the Boundary
geometric-motives construction. The motivic input is supplied elsewhere in the
Boundary stack: effective motives, the projective-line Tate object, and the
Tate-twist endofunctor.

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

/-- Tate-stabilized object type for a chosen Tate endofunctor. -/
abbrev StabilizedObject
    {C : Type u} [Category.{v} C]
    (_T : C ⥤ C) :=
  FormalTateStabilizedObject C

/-- The lightweight category structure used by the Boundary construction
surface. Morphisms are inherited from the effective object component; the
Tate-degree bookkeeping is object-level data. -/
instance stabilizedObjectCategory
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) : Category (StabilizedObject T) where
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

/-- Formal Tate stabilization of an effective category at a Tate endofunctor. -/
abbrev DMgmQ_Q
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateEndofunctor : DMgmEffQ_Q ⥤ DMgmEffQ_Q) :=
  StabilizedObject tateEndofunctor

/-- Directly named Tate stabilization of an effective category. -/
abbrev TateStabilization
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateEndofunctor : DMgmEffQ_Q ⥤ DMgmEffQ_Q) :=
  DMgmQ_Q DMgmEffQ_Q tateEndofunctor

/-- Alias emphasizing that `DMgm` is obtained from the effective layer by
Tate stabilization. -/
abbrev DMgmFromEffective
    (DMgmEffQ_Q : Type u)
    [Category.{v} DMgmEffQ_Q]
    (tateEndofunctor : DMgmEffQ_Q ⥤ DMgmEffQ_Q) :=
  TateStabilization DMgmEffQ_Q tateEndofunctor

/-- Embed effective objects as Tate-degree-zero stabilized objects. -/
def effectiveEmbedding
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) :
    C ⥤ DMgmQ_Q C T where
  obj X := ⟨X, 0⟩
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
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

/-- Tate shift functor on the formal stabilization. -/
def tateShift
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) :
    DMgmQ_Q C T ⥤ DMgmQ_Q C T where
  obj := tateShiftObject
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-- Inverse Tate shift functor on the formal stabilization. -/
def inverseTateShift
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) :
    DMgmQ_Q C T ⥤ DMgmQ_Q C T where
  obj := inverseTateShiftObject
  map f := f
  map_id := by
    intro X
    rfl
  map_comp := by
    intro X Y Z f g
    rfl

/-- The formal Tate shift is an equivalence. -/
def tateShiftEquivalence
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) :
    DMgmQ_Q C T ≌ DMgmQ_Q C T where
  functor := tateShift T
  inverse := inverseTateShift T
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

end Boundary.Motives
