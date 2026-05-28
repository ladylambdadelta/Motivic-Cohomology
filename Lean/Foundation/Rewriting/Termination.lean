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
# Termination

This file defines termination interfaces for abstract reduction systems.
-/

universe u

namespace Foundation.Rewriting

namespace ReductionSystem

variable {α : Type u}

/-- Witness data for termination via well-foundedness of the reduction relation. -/
structure TerminatingData (R : ReductionSystem α) where
  wf : WellFounded R.step

/-- Witness data for accessibility from a starting point. -/
structure AccessibleFromData (R : ReductionSystem α) (a : α) where
  acc : Acc R.step a

theorem accessible_of_terminating
    (R : ReductionSystem α)
    (h : TerminatingData R)
    (a : α) :
    AccessibleFromData R a where
  acc := h.wf.apply a

end ReductionSystem

end Foundation.Rewriting
