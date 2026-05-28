/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:1752-1917 (localization and Nisnevich descent prerequisites feeding completion arguments)
- our_paper_draft.tex:1926-2088 (effective presentation, stabilization, and completion-facing steps)
- our_paper_draft.tex:2130-2166 (minimal package, derived soundness, and classical realization interfaces)
- our_paper_draft.tex:2501-2544 (presentation matching and infinity comparison constraints)
- our_paper_draft.tex:5700-5714 (pi0 comparison consequences that rely on completion-level compatibility)

Still missing in this file/module:
- Explicit TeX-label annotations on each exported completion theorem/structure.
- Dependency lemmas restated in the exact signatures required by the manuscript order.
- Export-level dependency graph entries documenting which theorem is consumed by which downstream stage.

Coverage intent for this file:
- Keep implementation live; avoid surrogate abstractions.
- Store manuscript-traceability obligations in this header until declaration-level tags are added.
-/

import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Exactness Transport

This file provides a minimal exactness-transport interface used by completion packaging.
-/

universe u v

namespace Foundation.Completion

open CategoryTheory

/-- A composable pair of morphisms. -/
structure ComposablePair {C : Type u} [Category C] (X Y Z : C) where
  f : X ⟶ Y
  g : Y ⟶ Z

/-- Witness data that a composable pair has zero composite. -/
structure ZeroCompositeData {C : Type u} [Category C] [Preadditive C]
    {X Y Z : C} (p : ComposablePair X Y Z) where
  zeroProof : p.f ≫ p.g = 0

/-- Data needed to transport zero-composite exactness along a functor. -/
structure ExactnessTransportData
    (C : Type u) (D : Type v)
    [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) where
  map_zero : ∀ {X Y : C} (f : X ⟶ Y), f = 0 → F.map f = 0

namespace ExactnessTransportData

variable {C : Type u} {D : Type v}
variable [Category C] [Category D] [Preadditive C] [Preadditive D]
variable {F : C ⥤ D}

/-- Transport a zero-composite witness across a functor with zero-map data. -/
theorem transport_zeroComposite
    (data : ExactnessTransportData C D F)
    {X Y Z : C} (p : ComposablePair X Y Z) :
    ZeroCompositeData p → ZeroCompositeData
      ({ f := F.map p.f, g := F.map p.g } :
        ComposablePair (F.obj X) (F.obj Y) (F.obj Z)) := by
  intro hwit
  have hmap : F.map (p.f ≫ p.g) = 0 := data.map_zero (p.f ≫ p.g) hwit.zeroProof
  exact ⟨by simpa [Functor.map_comp] using hmap⟩

end ExactnessTransportData

end Foundation.Completion
