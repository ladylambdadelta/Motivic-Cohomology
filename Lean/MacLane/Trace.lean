/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (generator-level primitives feeding raw trace expressions and rewrites)
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1752-1917 (geometric rewrite families: localization, Nisnevich, A1)
- our_paper_draft.tex:1926-2088 (effective presentation/stabilization dependencies consumed by trace realization)
- our_paper_draft.tex:2130-2166 (minimal package and classical realization interface)
- our_paper_draft.tex:2501-2544 (presentation matching and infinity-comparison bridge)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- A declaration-index table connecting each Trace submodule to exact labels and theorem IDs.

Coverage intent for this file:
- Keep Trace as an implementation layer, not a placeholder.
- Maintain this header as a chapter-level manuscript coverage ledger.
-/

import MacLane.Trace.Syntax
import MacLane.Trace.Certified
import MacLane.Trace.Doctrine
import MacLane.Trace.Boundary
import MacLane.Trace.Reconstruction
import MacLane.Trace.NormalForm
import MacLane.Trace.Holography
import MacLane.Trace.Category

/-!
# MacLane.Trace

## Final-Form No-Scaffold Mode

Work in final-form mode only:
- no mock/scaffold placeholders;
- no vacuous substitutes (`:= True`, `PUnit`, `Unit`, `Nonempty`, indiscrete
	relations, dummy carriers);
- no weakened theorem statements presented as final targets.

For trace foundations specifically: build the calculus intensionally first
(syntax, primitive/admin moves, certified derivations), then define realization
as a functor out of that calculus. Do not define the calculus as its semantic
image.

This chapter contains the project-specific trace calculus stack.

Authoritative definition layer:
- `Certified.lean` is the canonical definition of the trace calculus
	(raw syntax, 2-cells, trace equivalence/classes, certified traces,
	formal sums, and realization semantics).

Doctrine layer:
- `Doctrine.lean` defines localization doctrines (which geometric rules are
	admitted) and the constructive trace-category core interfaces built from
	localized calculus data.

Assembly layers:
- `Category.lean` builds the `Tcan` doctrine instance from certified traces.
- `Boundary.lean`, `Holography.lean`, and `Reconstruction.lean` state and package
	the boundary/reflection and reconstruction surfaces.
- `NormalForm.lean` supplies normalization infrastructure used by certification.
-/

namespace MacLane.Trace

end MacLane.Trace
