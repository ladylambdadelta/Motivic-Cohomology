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
# Confluence

This file defines confluence interfaces for abstract reduction systems.
-/

universe u

namespace Foundation.Rewriting

namespace ReductionSystem

variable {α : Type u}

/-- Witness data for local confluence (diamond property). -/
structure LocallyConfluentData (R : ReductionSystem α) where
  witness : ∀ ⦃a b c : α⦄, R.step a b → R.step a c → JoinableData R b c

/-- Witness data for global confluence in reflexive-transitive closure. -/
structure ConfluentData (R : ReductionSystem α) where
  witness : ∀ ⦃a b c : α⦄, R.RedStar a b → R.RedStar a c → JoinableData R b c

theorem locally_confluent_of_confluent
    (R : ReductionSystem α) (conf : ConfluentData R) :
    LocallyConfluentData R where
  witness a b c hab hac := conf.witness (R.step_redStar hab) (R.step_redStar hac)

end ReductionSystem

end Foundation.Rewriting
