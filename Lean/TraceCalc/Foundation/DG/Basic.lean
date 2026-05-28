import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.CategoryTheory.Preadditive.Basic

universe u v

namespace TraceCalc
namespace Foundation
namespace DG

/-!
# Foundational DG Interfaces

Canonical extraction module for the dg-category core used by the later
`H^0`, Karoubi, and pretriangulated constructions.

Source quarry audited:
- `TraceCalc.LayerA.CategoryInfra.FreeDG`

This file intentionally contains only the foundational dg interfaces and their
basic algebraic laws. It imports no legacy `LayerA` modules.
-/

/-- Minimal abstract dg-style interface: objects, hom-complexes, zero morphisms,
and a differential. -/
structure DGCategoryLike where
  Obj : Type u
  HomComplex : Obj → Obj → Type v
  zero : {X Y : Obj} → HomComplex X Y
  differential : {X Y : Obj} → HomComplex X Y → HomComplex X Y

namespace DGCategoryLike

def differentialSquaredZero (target : DGCategoryLike.{u, v}) : Prop :=
  ∀ {X Y : target.Obj} (f : target.HomComplex X Y),
    target.differential (target.differential f) = target.zero

end DGCategoryLike

structure DGCategoryLaws (target : DGCategoryLike.{u, v}) where
  differentialSquaredZero : target.differentialSquaredZero

structure DGCategoryData (target : DGCategoryLike.{u, v}) where
  laws : DGCategoryLaws target

/-- Standard dg-category interface: graded homs, additive structure,
degree-zero identities, degree-additive composition, and a degree-raising
differential. -/
structure StandardDGCategoryLike where
  Obj : Type u
  Hom : Obj → Obj → Int → Type v
  zero : {X Y : Obj} → (n : Int) → Hom X Y n
  add : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y n → Hom X Y n
  neg : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y n
  id : (X : Obj) → Hom X X 0
  comp : {X Y Z : Obj} → {i j : Int} → Hom X Y i → Hom Y Z j → Hom X Z (i + j)
  differential : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y (n + 1)

namespace StandardDGCategoryLike

def sub (target : StandardDGCategoryLike.{u, v})
    {X Y : target.Obj} (n : Int)
    (left right : target.Hom X Y n) : target.Hom X Y n :=
  target.add n left (target.neg n right)

abbrev CycleHom (target : StandardDGCategoryLike.{u, v})
    (X Y : target.Obj) : Type v :=
  { f : target.Hom X Y 0 // target.differential 0 f = target.zero 1 }

def boundaryRel (target : StandardDGCategoryLike.{u, v})
    {X Y : target.Obj} : target.CycleHom X Y → target.CycleHom X Y → Prop :=
  fun left right =>
    ∃ witness : target.Hom X Y (-1),
      target.differential (-1) witness = target.sub 0 left.1 right.1

def differentialSquaredZero (target : StandardDGCategoryLike.{u, v}) : Prop :=
  ∀ {X Y : target.Obj} (n : Int) (f : target.Hom X Y n),
    target.differential (n + 1) (target.differential n f) =
      (by simpa [Int.add_assoc] using target.zero (n + 2))

end StandardDGCategoryLike

structure StandardDGCategoryLaws (target : StandardDGCategoryLike.{u, v}) where
  add_assoc :
    ∀ {X Y : target.Obj} (n : Int)
      (a b c : target.Hom X Y n),
        target.add n (target.add n a b) c =
          target.add n a (target.add n b c)
  add_comm :
    ∀ {X Y : target.Obj} (n : Int)
      (a b : target.Hom X Y n),
        target.add n a b = target.add n b a
  zero_add :
    ∀ {X Y : target.Obj} (n : Int)
      (a : target.Hom X Y n),
        target.add n (target.zero n) a = a
  add_zero :
    ∀ {X Y : target.Obj} (n : Int)
      (a : target.Hom X Y n),
        target.add n a (target.zero n) = a
  add_left_neg :
    ∀ {X Y : target.Obj} (n : Int)
      (a : target.Hom X Y n),
        target.add n (target.neg n a) a = target.zero n
  id_comp :
    ∀ {X Y : target.Obj} (f : target.Hom X Y 0),
      target.comp (target.id X) f = f
  comp_id :
    ∀ {X Y : target.Obj} (f : target.Hom X Y 0),
      target.comp f (target.id Y) = f
  comp_assoc :
    ∀ {W X Y Z : target.Obj}
      {i j k : Int}
      (f : target.Hom W X i)
      (g : target.Hom X Y j)
      (h : target.Hom Y Z k),
        target.comp (target.comp f g) h =
          (by simpa [Int.add_assoc] using target.comp f (target.comp g h))
  comp_zero_left :
    ∀ {X Y Z : target.Obj} {i j : Int}
      (g : target.Hom Y Z j),
        target.comp (target.zero (X := X) (Y := Y) i) g =
          target.zero (X := X) (Y := Z) (i + j)
  comp_zero_right :
    ∀ {X Y Z : target.Obj} {i j : Int}
      (f : target.Hom X Y i),
        target.comp f (target.zero (X := Y) (Y := Z) j) =
          target.zero (X := X) (Y := Z) (i + j)
  comp_add_left :
    ∀ {X Y Z : target.Obj} {i j : Int}
      (f₁ f₂ : target.Hom X Y i)
      (g : target.Hom Y Z j),
        target.comp (target.add i f₁ f₂) g =
          target.add (i + j) (target.comp f₁ g) (target.comp f₂ g)
  comp_add_right :
    ∀ {X Y Z : target.Obj} {i j : Int}
      (f : target.Hom X Y i)
      (g₁ g₂ : target.Hom Y Z j),
        target.comp f (target.add j g₁ g₂) =
          target.add (i + j) (target.comp f g₁) (target.comp f g₂)
  differential_zero :
    ∀ {X Y : target.Obj} (n : Int),
      target.differential n (target.zero (X := X) (Y := Y) n) =
        target.zero (X := X) (Y := Y) (n + 1)
  differential_add :
    ∀ {X Y : target.Obj} (n : Int)
      (a b : target.Hom X Y n),
        target.differential n (target.add n a b) =
          target.add (n + 1) (target.differential n a) (target.differential n b)
  differential_neg :
    ∀ {X Y : target.Obj} (n : Int)
      (a : target.Hom X Y n),
        target.differential n (target.neg n a) =
          target.neg (n + 1) (target.differential n a)
  differential_squaredZero : target.differentialSquaredZero
  id_closed :
    ∀ X : target.Obj,
      target.differential 0 (target.id X) = target.zero 1
  closed_comp :
    ∀ {X Y Z : target.Obj}
      (f : target.CycleHom X Y)
      (g : target.CycleHom Y Z),
        target.differential 0 (target.comp f.1 g.1) = target.zero 1

structure StandardDGCategoryData (target : StandardDGCategoryLike.{u, v}) where
  laws : StandardDGCategoryLaws target

namespace StandardDGCategoryData

instance instAddCommGroupHom {target : StandardDGCategoryLike.{u, v}}
    (data : StandardDGCategoryData target) (X Y : target.Obj) (n : Int) :
    AddCommGroup (target.Hom X Y n) := by
  let _ : Add (target.Hom X Y n) := ⟨target.add n⟩
  let _ : Zero (target.Hom X Y n) := ⟨target.zero n⟩
  let _ : Neg (target.Hom X Y n) := ⟨target.neg n⟩
  letI : AddGroup (target.Hom X Y n) :=
    AddGroup.ofLeftAxioms (data.laws.add_assoc n) (data.laws.zero_add n)
      (data.laws.add_left_neg n)
  let addGroupInst : AddGroup (target.Hom X Y n) := inferInstance
  exact
    { addGroupInst with
      add_comm := data.laws.add_comm n }

end StandardDGCategoryData

/-- Object-level extension data for the free dg envelope. -/
structure FreeDGUniversalProperty
    (presentation : Type u)
    (envelopeObj : Type u)
    (includeObj : presentation → envelopeObj) where
  liftObj : ∀ {D : Type u}, (ι : presentation → D) → envelopeObj → D
  lift_include :
    ∀ {D : Type u} (ι : presentation → D) (p : presentation),
      liftObj ι (includeObj p) = ι p

/-- Abstract free-dg-envelope package for a presentation type. -/
structure FreeDGEnvelope (presentation : Type u) where
  envelope : DGCategoryLike.{u, v}
  includeObj : presentation → envelope.Obj
  universalProperty : FreeDGUniversalProperty presentation envelope.Obj includeObj

end DG
end Foundation
end TraceCalc