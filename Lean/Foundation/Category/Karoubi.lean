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

import Foundation.Category.Idempotents
import Mathlib.CategoryTheory.Idempotents.Karoubi

/-!
# Karoubi Completion

This file exposes a minimal wrapper around mathlib's Karoubi completion.
-/

universe u

namespace Foundation.Category

open CategoryTheory

/-- The Karoubi completion of a category. -/
abbrev KaroubiCompletion (C : Type u) [Category C] : Type u :=
  CategoryTheory.Idempotents.Karoubi C

/-- Canonical embedding into the Karoubi completion. -/
abbrev toKaroubi (C : Type u) [Category C] : C ⥤ KaroubiCompletion C :=
  CategoryTheory.Idempotents.toKaroubi C

@[simp] def karoubiOfObject (C : Type u) [Category C] (X : C) : KaroubiCompletion C :=
  ((X : C) : CategoryTheory.Idempotents.Karoubi C)

@[simp] theorem karoubiOfObject_X (C : Type u) [Category C] (X : C) :
    (karoubiOfObject C X).X = X :=
  rfl

/-- Karoubi completion is idempotent complete. -/
theorem karoubi_idempotent_complete (C : Type u) [Category C] :
    CategoryTheory.IsIdempotentComplete (KaroubiCompletion C) :=
  inferInstance

end Foundation.Category
