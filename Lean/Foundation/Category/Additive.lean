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

import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Additive Categories

This file provides a minimal reusable additive-category surface for the foundation layer:

- a bundled context carrying preadditive and finite-biproduct structure;
- basic linearity lemmas for composition in preadditive categories.
-/

universe u

namespace Foundation.Category

open CategoryTheory
open CategoryTheory.Limits

/-- Minimal bundled additive context used by downstream interfaces. -/
structure AdditiveContext (C : Type u) [Category C] where
  toPreadditive : Preadditive C
  toHasFiniteBiproducts : HasFiniteBiproducts C

attribute [instance] AdditiveContext.toPreadditive
attribute [instance] AdditiveContext.toHasFiniteBiproducts

namespace AdditiveContext

/-- Build an additive context from existing typeclass instances. -/
def ofTypeclass (C : Type u) [Category C] [Preadditive C] [HasFiniteBiproducts C] :
    AdditiveContext C where
  toPreadditive := inferInstance
  toHasFiniteBiproducts := inferInstance

end AdditiveContext

section PreadditiveLemmas

variable {C : Type u} [Category C] [Preadditive C]
variable {W X Y Z : C}

@[simp] theorem zero_comp_hom (f : X ⟶ Y) :
    (0 : W ⟶ X) ≫ f = 0 := by
  simp

@[simp] theorem comp_zero_hom (f : X ⟶ Y) :
    f ≫ (0 : Y ⟶ Z) = 0 := by
  simp

@[simp] theorem add_comp_hom (f g : W ⟶ X) (h : X ⟶ Y) :
    (f + g) ≫ h = f ≫ h + g ≫ h := by
  simp

@[simp] theorem comp_add_hom (f : W ⟶ X) (g h : X ⟶ Y) :
    f ≫ (g + h) = f ≫ g + f ≫ h := by
  simp

@[simp] theorem neg_comp_hom (f : W ⟶ X) (h : X ⟶ Y) :
    (-f) ≫ h = -(f ≫ h) := by
  simp

@[simp] theorem comp_neg_hom (f : W ⟶ X) (h : X ⟶ Y) :
    f ≫ (-h) = -(f ≫ h) := by
  simp

@[simp] theorem sub_comp_hom (f g : W ⟶ X) (h : X ⟶ Y) :
    (f - g) ≫ h = f ≫ h - g ≫ h := by
  calc
    (f - g) ≫ h = (f + (-g)) ≫ h := by simp [sub_eq_add_neg]
    _ = f ≫ h + ((-g) ≫ h) := add_comp_hom f (-g) h
    _ = f ≫ h - g ≫ h := by simp [sub_eq_add_neg, neg_comp_hom]

@[simp] theorem comp_sub_hom (f : W ⟶ X) (g h : X ⟶ Y) :
    f ≫ (g - h) = f ≫ g - f ≫ h := by
  calc
    f ≫ (g - h) = f ≫ (g + (-h)) := by simp [sub_eq_add_neg]
    _ = f ≫ g + (f ≫ (-h)) := comp_add_hom f g (-h)
    _ = f ≫ g - f ≫ h := by simp [sub_eq_add_neg, comp_neg_hom]

end PreadditiveLemmas

end Foundation.Category
