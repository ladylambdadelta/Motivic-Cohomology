/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:1752-1917 (localization and descent mechanisms using quotient/reduction behavior)
- our_paper_draft.tex:1926-2088 (effective presentation and stabilization, which require normal-form/quotient discipline)
- our_paper_draft.tex:2130-2166 (minimal-package soundness requiring rewrite admissibility discipline)
- our_paper_draft.tex:2501-2544 (comparison compatibility constraints that rely on rewriting invariants)
- our_paper_draft.tex:5700-5714 (pi0 comparison stage requiring quotient invariance)

Still missing in this file/module:
- Per-theorem manuscript labels attached to the exported rewriting API.
- Explicit statements of invariants needed by downstream motive and trace layers.
- Dependency exports in the exact signatures consumed by `Trace.NormalForm` and motive-comparison modules.

Coverage intent for this file:
- Keep implementation live and foundational.
- Treat this header as the temporary manuscript-proof coverage ledger for rewriting infrastructure.
-/

import Mathlib.Logic.Relation

/-!
# Abstract Reduction Systems

This file provides reusable reduction-system interfaces and closure operations.
-/

universe u

namespace Foundation.Rewriting

/-- An abstract one-step reduction relation. -/
structure ReductionSystem (α : Type u) where
  step : α → α → Prop

namespace ReductionSystem

variable {α : Type u}

/-- Reflexive-transitive closure of the one-step relation. -/
abbrev RedStar (R : ReductionSystem α) : α → α → Prop :=
  Relation.ReflTransGen R.step

/-- Witness data that an element is in normal form. -/
structure NormalFormData (R : ReductionSystem α) (a : α) where
  no_step : ∀ b : α, ¬ R.step a b

/-- Witness data for joinability in the reflexive-transitive closure. -/
structure JoinableData (R : ReductionSystem α) (a b : α) where
  join : α
  left_red : R.RedStar a join
  right_red : R.RedStar b join

theorem redStar_refl (R : ReductionSystem α) (a : α) : R.RedStar a a :=
  Relation.ReflTransGen.refl

theorem step_redStar (R : ReductionSystem α) {a b : α} (h : R.step a b) :
    R.RedStar a b :=
  Relation.ReflTransGen.single h

end ReductionSystem

end Foundation.Rewriting
