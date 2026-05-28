/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (generator-level operations whose realization pipelines depend on DG interfaces)
- our_paper_draft.tex:1926-2088 (effective presentation and stabilization layer, which depends on DG infrastructure)
- our_paper_draft.tex:2130-2166 (minimal-package and classical-realization stages requiring DG functorial consistency)
- our_paper_draft.tex:2501-2544 (comparison constructions requiring DG-level functorial control)
- our_paper_draft.tex:5700-5714 (pi0 comparison consequences that use DG/H0 compatibility)

Still missing in this file/module:
- A precise TeX-label-to-Lean symbol index for DG primitives used by the motive pipeline.
- Explicit bridge lemmas documenting where DG facts feed manuscript theorem statements.
- Export contracts pinned to downstream users (`H0`, completion, trace realization) with exact dependency signatures.

Coverage intent for this file:
- Keep implementation live and reusable.
- Use this header as the manuscript proof-coverage checkpoint until per-symbol labeling is complete.
-/

import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Canonical DG Foundations

This module is the first canonical extraction from the legacy `TraceCalc`
infrastructure. It contains only the audited dg-category core needed for later
`H0`, Karoubi, and pretriangulated constructions.

Extraction source:
- `TraceCalc.LayerA.CategoryInfra.FreeDG`

Constraints:
- no imports from legacy `TraceCalc` modules
- no placeholder theorem targets
- no project-specific motivic terminology
-/

universe u v

namespace Foundation
namespace DG

/-- Minimal abstract dg-category interface, retaining only objects, hom-complexes, and the
differential. -/
structure RawDGCategory where
  Obj : Type u
  HomComplex : Obj → Obj → Type v
  zero : {X Y : Obj} → HomComplex X Y
  differential : {X Y : Obj} → HomComplex X Y → HomComplex X Y

namespace RawDGCategory

/-- Witness data that the differential squares to zero. -/
structure DifferentialSquaredZeroData (target : RawDGCategory.{u, v}) where
  witness : ∀ {X Y : target.Obj} (f : target.HomComplex X Y),
    target.differential (target.differential f) = target.zero

end RawDGCategory

structure RawDGCategoryLaws (target : RawDGCategory.{u, v}) where
  differential_squared_zero : RawDGCategory.DifferentialSquaredZeroData target

structure RawDGCategoryData (target : RawDGCategory.{u, v}) where
  laws : RawDGCategoryLaws target

/-- Standard dg-category interface: graded homs, additive structure,
degree-zero identities, degree-additive composition, and a degree-raising
differential. -/
structure GradedDGCategory where
  Obj : Type u
  Hom : Obj → Obj → Int → Type v
  zero : {X Y : Obj} → (n : Int) → Hom X Y n
  add : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y n → Hom X Y n
  neg : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y n
  id : (X : Obj) → Hom X X 0
  comp : {X Y Z : Obj} → {i j : Int} → Hom X Y i → Hom Y Z j → Hom X Z (i + j)
  differential : {X Y : Obj} → (n : Int) → Hom X Y n → Hom X Y (n + 1)

namespace GradedDGCategory

/-- Witness data for graded differential squaring to zero. -/
structure DifferentialSquaredZeroData (target : GradedDGCategory.{u, v}) where
  witness : ∀ {X Y : target.Obj} (n : Int) (f : target.Hom X Y n),
    target.differential (n + 1) (target.differential n f) =
      target.zero (n + 1 + 1)

def sub (target : GradedDGCategory.{u, v})
    {X Y : target.Obj} (n : Int)
    (left right : target.Hom X Y n) : target.Hom X Y n :=
  target.add n left (target.neg n right)

abbrev CycleHom (target : GradedDGCategory.{u, v})
    (X Y : target.Obj) : Type v :=
  { f : target.Hom X Y 0 // target.differential 0 f = target.zero 1 }

def boundary_rel (target : GradedDGCategory.{u, v})
    {X Y : target.Obj} : target.CycleHom X Y → target.CycleHom X Y → Prop :=
  fun left right =>
    ∃ witness : target.Hom X Y (-1),
      target.differential (-1) witness = target.sub 0 left.1 right.1

end GradedDGCategory

structure GradedDGCategoryLaws (target : GradedDGCategory.{u, v}) where
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
          (Int.add_assoc i j k ▸ target.comp f (target.comp g h))
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
  differential_squared_zero :
    ∀ {X Y : target.Obj} (n : Int) (f : target.Hom X Y n),
      target.differential (n + 1) (target.differential n f) =
        target.zero (n + 1 + 1)
  id_closed :
    ∀ X : target.Obj,
      target.differential 0 (target.id X) = target.zero 1
  closed_comp :
    ∀ {X Y Z : target.Obj}
      (f : target.CycleHom X Y)
      (g : target.CycleHom Y Z),
        target.differential 0 (target.comp f.1 g.1) = target.zero 1

structure GradedDGCategoryData (target : GradedDGCategory.{u, v}) where
  laws : GradedDGCategoryLaws target

namespace GradedDGCategoryData

instance instAddCommGroupHom {target : GradedDGCategory.{u, v}}
    (data : GradedDGCategoryData target) (X Y : target.Obj) (n : Int) :
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

end GradedDGCategoryData

end DG
end Foundation
