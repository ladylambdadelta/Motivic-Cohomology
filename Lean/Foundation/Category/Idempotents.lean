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
# Idempotent Splittings

This file contains a minimal reusable surface for idempotents and their splittings.
-/

universe u

namespace Foundation.Category

open CategoryTheory

/-- A typed idempotent endomorphism. -/
structure IdempotentData {C : Type u} [Category C] (X : C) where
  arrow : X ⟶ X
  idem : arrow ≫ arrow = arrow

/-- A splitting of an idempotent. -/
structure IdempotentSplitting {C : Type u} [Category C] {X : C}
    (p : IdempotentData X) where
  Y : C
  i : X ⟶ Y
  r : Y ⟶ X
  retract : r ≫ i = 𝟙 Y
  split_eq : i ≫ r = p.arrow

namespace IdempotentSplitting

variable {C : Type u} [Category C] {X : C} {p : IdempotentData X}

@[simp] theorem section_idempotent (s : IdempotentSplitting p) :
    (s.i ≫ s.r) ≫ (s.i ≫ s.r) = s.i ≫ s.r := by
  calc
    (s.i ≫ s.r) ≫ (s.i ≫ s.r)
        = s.i ≫ (s.r ≫ s.i) ≫ s.r := by simp [Category.assoc]
    _ = s.i ≫ 𝟙 s.Y ≫ s.r := by rw [s.retract]
    _ = s.i ≫ s.r := by simp

@[simp] theorem split_arrow_eq (s : IdempotentSplitting p) :
    s.i ≫ s.r = p.arrow :=
  s.split_eq

/-- A splitting canonically produces an idempotent. -/
def toIdempotent (s : IdempotentSplitting p) : IdempotentData X where
  arrow := s.i ≫ s.r
  idem := s.section_idempotent

end IdempotentSplitting

end Foundation.Category
