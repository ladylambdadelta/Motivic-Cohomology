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
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Monoidal Contexts

Minimal bundled carrier for the tensor/unit data of a monoidal category.

A `MonoidalContext` packages the object-level tensor and unit without laws, allowing
structures to record monoidal data independently of the coherence axioms.  Law witnesses
are provided separately (e.g. `MonoidalContextLaws`).
-/

universe u

namespace Foundation.Category

open CategoryTheory

/-- Object-level data of a monoidal category: a binary tensor and a unit object. -/
structure MonoidalContext (C : Type u) [Category C] where
  /-- Binary tensor product on objects. -/
  tensorObj : C → C → C
  /-- Monoidal unit object. -/
  unitObj : C

/-- Laws a monoidal context must satisfy to be a genuine monoidal category. -/
structure MonoidalContextLaws {C : Type u} [Category C] (M : MonoidalContext C) where
  /-- Associativity: (X ⊗ Y) ⊗ Z ≅ X ⊗ (Y ⊗ Z). Stored as object-level equality for strict monoidal. -/
  assoc : ∀ (X Y Z : C), M.tensorObj (M.tensorObj X Y) Z = M.tensorObj X (M.tensorObj Y Z)
  /-- Left unit law: 1 ⊗ X = X. -/
  left_unit : ∀ (X : C), M.tensorObj M.unitObj X = X
  /-- Right unit law: X ⊗ 1 = X. -/
  right_unit : ∀ (X : C), M.tensorObj X M.unitObj = X

namespace MonoidalContext

/-- The left-projection monoidal context: X ⊗ Y := X, unit := X₀.

    This satisfies the right unit law (X ⊗ 1 = X) but not the left unit law (1 ⊗ X = 1 ≠ X
    in general).  It is useful as a degenerate test instance and for monoidal structures
    where the second factor is always discarded. -/
def leftProjection (C : Type u) [Category C] (X₀ : C) : MonoidalContext C where
  tensorObj := fun X _ => X
  unitObj   := X₀

/-- The right-projection monoidal context: X ⊗ Y := Y, unit := X₀.

    Satisfies the left unit law (1 ⊗ X = X) but not the right unit law. -/
def rightProjection (C : Type u) [Category C] (X₀ : C) : MonoidalContext C where
  tensorObj := fun _ Y => Y
  unitObj   := X₀

/-- A constant monoidal context: X ⊗ Y := X₀ for all X Y.

    Satisfies neither unit law unless the unit itself is X₀, which is trivially true; use
    only for degenerate base cases. -/
def constant (C : Type u) [Category C] (X₀ : C) : MonoidalContext C where
  tensorObj := fun _ _ => X₀
  unitObj   := X₀

end MonoidalContext

end Foundation.Category
