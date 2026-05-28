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

import Mathlib.CategoryTheory.Category.Basic

/-!
# Monoidal Transport Through Completion

This file provides a minimal monoidal transport interface for completion packages.
-/

universe u v

namespace Foundation.Completion

open CategoryTheory

/-- Explicit tensor-compatibility witness data. -/
structure TensorCompatibilityData {C : Type u} {D : Type v}
    [Category C] [Category D]
    (obj : C → D) (tensorObjC : C → C → C) (tensorObjD : D → D → D) where
  onObj : ∀ X Y : C, obj (tensorObjC X Y) = tensorObjD (obj X) (obj Y)

/-- Explicit unit-compatibility witness data. -/
structure UnitCompatibilityData {C : Type u} {D : Type v}
    [Category C] [Category D]
    (obj : C → D) (unitObjC : C) (unitObjD : D) where
  onObj : obj unitObjC = unitObjD

/-- Monoidal transport data for a completion-style comparison functor. -/
structure MonoidalTransportData
    (C : Type u) (D : Type v)
    [Category C] [Category D] where
  obj : C → D
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)
  map_id : ∀ X : C, map (𝟙 X) = 𝟙 (obj X)
  map_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z), map (f ≫ g) = map f ≫ map g
  tensorObjC : C → C → C
  tensorObjD : D → D → D
  unitObjC : C
  unitObjD : D
  tensorCompatData : TensorCompatibilityData obj tensorObjC tensorObjD
  unitCompatData : UnitCompatibilityData obj unitObjC unitObjD

namespace MonoidalTransportData

variable {C : Type u} {D : Type v}
variable [Category C] [Category D]

@[simp] theorem map_comp_assoc
    (T : MonoidalTransportData C D)
    {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    T.map (f ≫ g ≫ h) = T.map f ≫ T.map g ≫ T.map h := by
  rw [T.map_comp, T.map_comp]

end MonoidalTransportData

end Foundation.Completion
