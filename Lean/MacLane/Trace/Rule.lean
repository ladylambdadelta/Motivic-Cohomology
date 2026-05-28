/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (generator-level primitives and formal operations that appear in raw trace syntax)
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1752-1917 (rewrite-rule families and admissibility)
- our_paper_draft.tex:2130-2166 (minimal package interfaces consuming rule-level semantics)
- our_paper_draft.tex:2501-2544 (comparison bridge constraints via rule semantics)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- Per-rule-family mapping from constructors to exact manuscript theorem labels.

Coverage intent for this file:
- Preserve the intensional rule-shape implementation.
- Use this header as the rule-level manuscript coverage ledger.
-/

import MacLane.Trace.Syntax

/-!
# Trace Rule Shapes

Raw trace expressions and geometric rewrite-rule shapes used by doctrine-relative
certified trace calculi.
-/

namespace MacLane.Trace

open Geometry.Schemes Geometry.Generators

/-- Raw trace expressions: the generators of the free compact closed category
    on `CanonicalWord gens`. -/
inductive RawTraceExpr (gens : List SchemeOverQ) :
    CanonicalWord gens → CanonicalWord gens → Type where
  | id     : ∀ (w : CanonicalWord gens),
               RawTraceExpr gens w w
  | comp   : ∀ {s t u : CanonicalWord gens},
               RawTraceExpr gens s t → RawTraceExpr gens t u →
               RawTraceExpr gens s u
  | tensor : ∀ {s₁ t₁ s₂ t₂ : CanonicalWord gens},
               RawTraceExpr gens s₁ t₁ → RawTraceExpr gens s₂ t₂ →
               RawTraceExpr gens (CanonicalWord.tensor s₁ s₂)
                                 (CanonicalWord.tensor t₁ t₂)
  | eval   : ∀ (w : CanonicalWord gens),
               RawTraceExpr gens
                 (CanonicalWord.tensor (CanonicalWord.dual w) w)
                 CanonicalWord.unit
  | coeval : ∀ (w : CanonicalWord gens),
               RawTraceExpr gens
                 CanonicalWord.unit
                 (CanonicalWord.tensor w (CanonicalWord.dual w))

/-- A geometric rewrite rule in the motivic trace calculus. -/
structure GeometricRewriteRule (gens : List SchemeOverQ) where
  name        : String
  sourceShape : CanonicalWord gens
  targetShape : CanonicalWord gens
  lhs         : RawTraceExpr gens sourceShape targetShape
  rhs         : RawTraceExpr gens sourceShape targetShape

end MacLane.Trace
