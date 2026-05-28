/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (geometric generators and primitive families requiring additive ambient structure)
- our_paper_draft.tex:1752-1917 (localization/descent interfaces using categorical exactness and quotient discipline)
- our_paper_draft.tex:1926-2088 (effective presentation and stabilization statements relying on additive/localization infrastructure)
- our_paper_draft.tex:2130-2166 (minimal package and classical realization steps that consume additive functoriality)
- our_paper_draft.tex:2501-2544 (presentation matching and infinity-level comparison functoriality)
- our_paper_draft.tex:5700-5714 (pi0 comparison compatibility obligations)

Still missing in this file/module:
- A declaration-by-declaration map from Lean symbols in this file to exact TeX labels used downstream.
- Theorems in the precise signatures required by the DMgm assembly chain (no adapter lemmas yet).
- Explicit downstream-use ledger showing which exports feed Presentation, Stabilization, and Comparison stages.

Coverage intent for this file:
- Keep this file implementation-active.
- Use this header as the manuscript traceability surface until per-declaration TeX tags are added.
-/

import Mathlib.CategoryTheory.Category.Basic

/-!
# Categorical Localization

This file provides a minimal proof-carrying interface for localization data,
including an explicit zigzag model scaffold.
-/

universe u v

namespace Foundation.Category

open CategoryTheory

/-- A class of weak equivalences in a category. -/
structure WeakEquivalences (C : Type u) [Category C] where
  W : ∀ {X Y : C}, (X ⟶ Y) → Prop
  id_mem : ∀ X : C, W (𝟙 X)
  comp_mem : ∀ {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}, W f → W g → W (f ≫ g)

/-- Local witness that a morphism is invertible. -/
structure InvertibleData {C : Type u} [Category C] {X Y : C} (f : X ⟶ Y) where
  inv : Y ⟶ X
  left_inv : f ≫ inv = 𝟙 X
  right_inv : inv ≫ f = 𝟙 Y

/-- Presentation data for roof/zigzag localization. -/
abbrev LocalizingMorphismPresentation (C : Type u) [Category C] :=
  WeakEquivalences C

/-- One step in a zigzag: either a forward morphism, or a backward weak equivalence. -/
inductive ZigzagStep {C : Type u} [Category C]
    (W : LocalizingMorphismPresentation C) : C → C → Type u where
  | forward {X Y : C} (f : X ⟶ Y) : ZigzagStep W X Y
  | backward {X Y : C} (w : Y ⟶ X) (hw : W.W w) : ZigzagStep W X Y

/-- Finite zigzags between objects. -/
inductive ZigzagHom {C : Type u} [Category C]
    (W : LocalizingMorphismPresentation C) : C → C → Type u where
  | nil (X : C) : ZigzagHom W X X
  | cons {X Y Z : C} : ZigzagStep W X Y → ZigzagHom W Y Z → ZigzagHom W X Z

namespace ZigzagHom

variable {C : Type u} [Category C]
variable {W : LocalizingMorphismPresentation C}

/-- Concatenate two zigzags. -/
def comp {X Y Z : C}
    (left : ZigzagHom W X Y)
    (right : ZigzagHom W Y Z) : ZigzagHom W X Z :=
  match left with
  | nil _ => right
  | cons step tail => cons step (comp tail right)

@[simp] theorem nil_comp {X Y : C} (z : ZigzagHom W X Y) :
    comp (ZigzagHom.nil X) z = z :=
  rfl

@[simp] theorem comp_nil {X Y : C} (z : ZigzagHom W X Y) :
    comp z (ZigzagHom.nil Y) = z := by
  induction z with
  | nil _ => rfl
  | cons _ tail ih => simp [comp, ih]

end ZigzagHom

/-- Localization data: a comparison functor-like map that inverts weak equivalences. -/
structure LocalizationData
    (C : Type u) (D : Type v) [Category C] [Category D]
    (weq : WeakEquivalences C) where
  QObj : C → D
  QMap : ∀ {X Y : C}, (X ⟶ Y) → (QObj X ⟶ QObj Y)
  map_id : ∀ X : C, QMap (𝟙 X) = 𝟙 (QObj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), QMap (f ≫ g) = QMap f ≫ QMap g
  inverts : ∀ {X Y : C} (f : X ⟶ Y), weq.W f → InvertibleData (QMap f)

namespace LocalizationData

variable {C : Type u} {D : Type v} [Category C] [Category D]
variable {weq : WeakEquivalences C}

/-- Transport localized objects along equality of source objects. -/
def transportQObj (L : LocalizationData C D weq) {X Y : C} (h : X = Y) :
    L.QObj X = L.QObj Y := by
  cases h
  rfl

@[simp] theorem map_comp_assoc (L : LocalizationData C D weq)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    L.QMap (f ≫ g ≫ h) = L.QMap f ≫ L.QMap g ≫ L.QMap h := by
  rw [L.map_comp, L.map_comp]

end LocalizationData

end Foundation.Category
