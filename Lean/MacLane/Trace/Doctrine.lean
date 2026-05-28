/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1752-1917 (localization/Nisnevich/A1 rewrite admissibility conditions)
- our_paper_draft.tex:1926-2088 (effective/stable assembly depending on doctrine admissibility)
- our_paper_draft.tex:2130-2166 (minimal package and realization interfaces)
- our_paper_draft.tex:2501-2544 (comparison bridge through doctrine-level equivalence constraints)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- A doctrine-index table connecting each admissibility constructor family to its TeX source label.

Coverage intent for this file:
- Preserve proof-relevant doctrine structures.
- Keep this header as the doctrine-level manuscript obligations ledger.
-/

import MacLane.Trace.Rule

/-!
# Trace Doctrine

Proof-relevant doctrine interface controlling geometric rewrite admissibility.
-/

namespace MacLane.Trace

/-- A trace doctrine on `gens` specifies the proof-relevant admissibility type
for each geometric rewrite rule. -/
structure TraceDoctrine (gens : List Geometry.Schemes.SchemeOverQ) where
  Admissible : GeometricRewriteRule gens → Type

end MacLane.Trace
