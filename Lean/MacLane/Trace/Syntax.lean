/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:484-814 (generator families and formal operations underlying canonical words)
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1752-1917 (localization/A1/Nis contexts that constrain rewrite syntax)
- our_paper_draft.tex:1926-2088 (effective/stable assembly that consumes canonical word normal forms)
- our_paper_draft.tex:2501-2544 (comparison bridge requiring syntax-level normalization coherence)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- A per-rewrite-rule label map for all word-step constructors and normal-form obligations.

Coverage intent for this file:
- Preserve the canonical-word syntax implementation.
- Use this header as the syntax-level manuscript coverage ledger.
-/

import Geometry.Generators.Families
import Foundation.Rewriting.AbstractReduction
import Foundation.Rewriting.NormalForms

/-!
# Canonical Word Syntax

## Final-Form Policy

This file defines permanent syntax objects only. Do not introduce surrogate
carriers or weakened surrogate statements to force progress.

Syntax here must remain intensional and proof-relevant: it is the source
language from which traces are built, not a semantic shadow or compressed
correspondence-level replacement.

The formal syntax of canonical words in the trace calculus.

A `CanonicalWord` over a generator list is a formal tensor expression built from:
- Individual generator schemes (smooth projective varieties over ℚ)
- The unit motive ℚ(0)
- Tate twists ℚ(n)
- Tensor products ⊗
- Internal duals (−)^∨
- Formal cohomological shifts [n]

The motivic reduction system reduces words to a canonical normal form using the
standard tensor-calculus identities. Confluence + termination guarantee uniqueness.
-/

namespace MacLane.Trace

open Geometry.Schemes Geometry.Generators
open Foundation.Rewriting

/-! ## The word type -/

/-- Formal canonical words over a fixed generator list. -/
inductive CanonicalWord (gens : List SchemeOverQ) : Type where
  | unit   : CanonicalWord gens
  | tate   : ℤ → CanonicalWord gens
  | gen    : Fin gens.length → CanonicalWord gens
  | tensor : CanonicalWord gens → CanonicalWord gens → CanonicalWord gens
  | dual   : CanonicalWord gens → CanonicalWord gens
  | shift  : ℤ → CanonicalWord gens → CanonicalWord gens
  deriving DecidableEq, Repr

namespace CanonicalWord

variable {gens : List SchemeOverQ}

/-- Tate-twist operation: M(n) = M ⊗ ℚ(n). -/
def twist (n : ℤ) (w : CanonicalWord gens) : CanonicalWord gens :=
  tensor w (tate n)

/-- The Lefschetz motive L = ℚ(1)[2]. -/
def lefschetz : CanonicalWord gens := shift 2 (tate 1)

/-- Formal cohomological weight (additive). -/
def weight : CanonicalWord gens → ℤ
  | unit       => 0
  | tate n     => -2 * n
  | gen _      => 0
  | tensor a b => weight a + weight b
  | dual w     => -(weight w)
  | shift n w  => weight w + n

/-- Size measure for termination arguments. -/
def size : CanonicalWord gens → ℕ
  | unit       => 0
  | tate _     => 0
  | gen _      => 1
  | tensor a b => size a + size b + 1
  | dual w     => size w + 1
  | shift _ w  => size w + 1

end CanonicalWord

/-! ## Reduction system -/

/-- Root one-step motivic reduction relation (no context closure). -/
inductive wordStepBase {gens : List SchemeOverQ} :
  CanonicalWord gens → CanonicalWord gens → Prop where
  | tensor_unit_left  : ∀ w,
    wordStepBase (.tensor .unit w) w
  | tensor_unit_right : ∀ w,
    wordStepBase (.tensor w .unit) w
  | dual_dual         : ∀ w,
    wordStepBase (.dual (.dual w)) w
  | tate_zero         : wordStepBase (.tate 0) .unit
  | tensor_tate       : ∀ m n,
    wordStepBase (.tensor (.tate m) (.tate n)) (.tate (m + n))
  | shift_zero        : ∀ w,
    wordStepBase (.shift 0 w) w
  | shift_shift       : ∀ m n w,
    wordStepBase (.shift m (.shift n w)) (.shift (m + n) w)

/-- One-step motivic reduction relation, closed under word contexts.

Standard tensor-calculus identities are generated at the root by
`wordStepBase`, then propagated through tensor/dual/shift contexts. -/
inductive wordStep {gens : List SchemeOverQ} :
  CanonicalWord gens → CanonicalWord gens → Prop where
  | base : ∀ {a b}, wordStepBase a b → wordStep a b
  | tensor_left : ∀ {a a' b},
    wordStep a a' → wordStep (.tensor a b) (.tensor a' b)
  | tensor_right : ∀ {a b b'},
    wordStep b b' → wordStep (.tensor a b) (.tensor a b')
  | dual : ∀ {a a'},
    wordStep a a' → wordStep (.dual a) (.dual a')
  | shift : ∀ n {a a'},
    wordStep a a' → wordStep (.shift n a) (.shift n a')

/-- The word reduction system. -/
def wordReductionSystem (gens : List SchemeOverQ) :
    ReductionSystem (CanonicalWord gens) where
  step := wordStep

/-! ## Normal form data -/

/-- A word is irreducible if no reduction step applies. -/
def IsIrreducible {gens : List SchemeOverQ} (w : CanonicalWord gens) : Prop :=
  (wordReductionSystem gens).NormalFormData w

/-- Canonical normal form witness for a word. -/
structure CanonicalNFData {gens : List SchemeOverQ} (w : CanonicalWord gens) where
  nf        : CanonicalWord gens
  reachable : (wordReductionSystem gens).RedStar w nf
  is_nf     : IsIrreducible nf

/-! ## Syntactic morphisms -/

/-- A word morphism: a formal source-target pair at the syntactic level. -/
structure WordMorphism (gens : List SchemeOverQ) where
  source : CanonicalWord gens
  target : CanonicalWord gens

/-- Syntactic equivalence of word morphisms: sources and targets have the same normal form. -/
structure WordMorphismEquivalence {gens : List SchemeOverQ}
    (f g : WordMorphism gens) where
  source_nf_f : CanonicalNFData f.source
  source_nf_g : CanonicalNFData g.source
  target_nf_f : CanonicalNFData f.target
  target_nf_g : CanonicalNFData g.target
  source_eq   : source_nf_f.nf = source_nf_g.nf
  target_eq   : target_nf_f.nf = target_nf_g.nf

end MacLane.Trace
