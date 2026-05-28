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

import Foundation.Rewriting.AbstractReduction

/-!
# Quotients of Rewriting Systems

This file provides quotient interfaces compatible with reduction relations.
-/

universe u

namespace Foundation.Rewriting

namespace ReductionSystem

variable {α : Type u}

/-- Quotient data for a reduction system. -/
structure ReductionQuotientData (R : ReductionSystem α) where
  setoid : Setoid α
  step_respects : ∀ {a b : α}, R.step a b → setoid.r a b

/-- Underlying quotient type. -/
abbrev QuotientType {R : ReductionSystem α} (Q : ReductionQuotientData R) : Type u :=
  Quotient Q.setoid

/-- Canonical quotient map. -/
def quotMap {R : ReductionSystem α} (Q : ReductionQuotientData R) : α → QuotientType Q :=
  Quotient.mk Q.setoid

theorem step_sound {R : ReductionSystem α} (Q : ReductionQuotientData R)
    {a b : α} (h : R.step a b) :
    quotMap Q a = quotMap Q b :=
  Quotient.sound (Q.step_respects h)

end ReductionSystem

end Foundation.Rewriting
