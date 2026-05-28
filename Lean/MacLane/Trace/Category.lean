/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1926-2088 (effective/stable assembly that consumes the trace doctrine)
- our_paper_draft.tex:2130-2166 (minimal package and realization interfaces for trace-category morphisms)
- our_paper_draft.tex:2501-2544 (presentation matching and infinity-comparison compatibility)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- An explicit equivalence-proof obligation list for well-defined composition/tensor under trace equivalence.

Coverage intent for this file:
- Preserve the current trace-category implementation.
- Treat this header as the category-level manuscript obligations ledger.
-/

import MacLane.Trace.Certified

/-!
# Trace Category

## Final-Form Policy

This file should construct the actual trace category from certified trace
objects. Do not substitute semantic shadows or abstract dummy targets for
categorical operations and laws.

Any open proof must be an exact theorem obligation in final mathematical form.

The canonical trace category `Tcan(gens)` as a `TraceDoctrine` instance.

## Design

The objects are `CanonicalWord gens` and the morphisms are
`FormalTraceMorphSum gens s t`: formal ℤ-linear combinations of
`TraceMorphism` values.

A `TraceMorphism` carries:
- `cls : TraceClass gens s t`              — the trace equivalence class
- `canonical : RawTraceExpr gens s t`      — a canonical representative
- `represents : TraceClass.mk canonical = cls` — coherence

No `TraceCertificate` is constructed in this file.  Normalization certificates
(`isNormal`, `twoCellCoverage`) are the obligation of `NormalForm.lean`, which
upgrades `TraceMorphism` to `CertifiedTrace` by supplying the full
four-component proof package.

Composition is implemented by syntactic composite:
  `comp f g = { canonical := .comp f.canonical g.canonical, … , represents := rfl }`

This is mathematically correct: `TraceClass.mk (.comp f.canonical g.canonical)` is
the trace class of the composite.  Well-definedness of composition on `TraceHom`
(the ℤ-module quotient) requires the congruence theorem for `TraceEquiv`, which is
a theorem obligation in `NormalForm.lean`.

## Key types

- `TraceMorphism gens s t`             — morphism presentation (no certificate)
- `FormalTraceMorphSum gens s t`       — ℤ-linear combination of `TraceMorphism`
- `TcanCategory gens : TraceDoctrine`  — the categorical structure
- `TcanCategoryLaws gens`              — object-level monoidal coherence laws
- `TcanData gens r := GenWitnesses r`  — alias for downstream geometric use
-/

namespace MacLane.Trace

open Geometry.Schemes

/-! ## TraceMorphism: morphism presentation without normalization certificate -/

/-- A **trace morphism presentation**: the trace equivalence class together
    with a chosen canonical representative and a coherence proof.

    The normalization certificate (`TraceCertificate`) is NOT carried here.
    It is supplied by `NormalForm.lean`, which upgrades a `TraceMorphism` to
    a `CertifiedTrace` by establishing `isNormal` and `twoCellCoverage`.

    `TraceMorphism` is the summand type of `FormalTraceMorphSum`, which is the
    `Hom` type for `TcanCategory`. -/
structure TraceMorphism (gens : List SchemeOverQ) (s t : CanonicalWord gens) where
  /-- The trace equivalence class: the morphism in the trace category. -/
  cls        : TraceClass gens s t
  /-- A canonical representative raw expression. -/
  canonical  : RawTraceExpr gens s t
  /-- Coherence: `canonical` represents `cls`. -/
  represents : TraceClass.mk canonical = cls

namespace TraceMorphism

/-- Identity trace morphism at word `w`. -/
def ofId {gens : List SchemeOverQ} (w : CanonicalWord gens) : TraceMorphism gens w w where
  cls        := TraceClass.mk (.id w)
  canonical  := .id w
  represents := rfl

/-- Sequential composition by syntactic composite.

    The canonical representative of `comp f g` is `.comp f.canonical g.canonical`.
    The trace class is `TraceClass.mk` of that composite.
    No normalization certificate is required or constructed. -/
def comp {gens : List SchemeOverQ} {s t u : CanonicalWord gens}
    (f : TraceMorphism gens s t) (g : TraceMorphism gens t u) :
    TraceMorphism gens s u where
  cls        := TraceClass.mk (.comp f.canonical g.canonical)
  canonical  := .comp f.canonical g.canonical
  represents := rfl

/-- Tensor product by syntactic tensor.

    The canonical representative of `tensor f g` is `.tensor f.canonical g.canonical`. -/
def tensor {gens : List SchemeOverQ}
    {s₁ t₁ s₂ t₂ : CanonicalWord gens}
    (f : TraceMorphism gens s₁ t₁)
    (g : TraceMorphism gens s₂ t₂) :
    TraceMorphism gens (CanonicalWord.tensor s₁ s₂) (CanonicalWord.tensor t₁ t₂) where
  cls        := TraceClass.mk (.tensor f.canonical g.canonical)
  canonical  := .tensor f.canonical g.canonical
  represents := rfl

/-- Evaluation morphism `ε_w : w^∨ ⊗ w → ℚ(0)`. -/
def ofEval {gens : List SchemeOverQ} (w : CanonicalWord gens) :
    TraceMorphism gens
      (CanonicalWord.tensor (CanonicalWord.dual w) w)
      CanonicalWord.unit where
  cls        := TraceClass.mk (.eval w)
  canonical  := .eval w
  represents := rfl

/-- Coevaluation morphism `η_w : ℚ(0) → w ⊗ w^∨`. -/
def ofCoeval {gens : List SchemeOverQ} (w : CanonicalWord gens) :
    TraceMorphism gens
      CanonicalWord.unit
      (CanonicalWord.tensor w (CanonicalWord.dual w)) where
  cls        := TraceClass.mk (.coeval w)
  canonical  := .coeval w
  represents := rfl

end TraceMorphism

/-! ## FormalTraceMorphSum: ℤ-linear combinations of TraceMorphism -/

/-- A **formal ℤ-linear combination of trace morphisms**.

    This is the `Hom` type for `TcanCategory`.  It is the list presentation
    of the hom-group; the actual abelian group is obtained by quotienting by
    coefficient-combining relations.

    Unlike `FormalTraceSum` (which requires `CertifiedTrace` in each summand),
    `FormalTraceMorphSum` uses `TraceMorphism` and requires no normalization
    certificate.  The certified upgrade is deferred to `NormalForm.lean`. -/
structure FormalTraceMorphSum (gens : List SchemeOverQ) (s t : CanonicalWord gens) where
  summands : List (ℤ × TraceMorphism gens s t)

namespace FormalTraceMorphSum

def zero {gens : List SchemeOverQ} {s t : CanonicalWord gens} :
    FormalTraceMorphSum gens s t := ⟨[]⟩

def add {gens : List SchemeOverQ} {s t : CanonicalWord gens}
    (f g : FormalTraceMorphSum gens s t) : FormalTraceMorphSum gens s t :=
  ⟨f.summands ++ g.summands⟩

def neg {gens : List SchemeOverQ} {s t : CanonicalWord gens}
    (f : FormalTraceMorphSum gens s t) : FormalTraceMorphSum gens s t :=
  ⟨f.summands.map fun (n, T) => (-n, T)⟩

/-- Sequential composition by bilinear extension.

    `(∑ nᵢ Tᵢ) ∘ (∑ mⱼ Sⱼ) = ∑ᵢⱼ nᵢ·mⱼ (Tᵢ ∘ Sⱼ)`

    Each composed summand uses `TraceMorphism.comp`, which records the syntactic
    composite `.comp Tᵢ.canonical Sⱼ.canonical` as canonical representative and
    `TraceClass.mk` of that composite as its class.  No certificate is constructed. -/
def comp {gens : List SchemeOverQ} {s t u : CanonicalWord gens}
    (f : FormalTraceMorphSum gens s t)
    (g : FormalTraceMorphSum gens t u) : FormalTraceMorphSum gens s u :=
  ⟨f.summands.flatMap fun (n, T_f) =>
    g.summands.map fun (m, T_g) => (n * m, T_f.comp T_g)⟩

/-- Tensor product of morphisms by bilinear extension.

    `(∑ nᵢ Tᵢ) ⊗ (∑ mⱼ Sⱼ) = ∑ᵢⱼ nᵢ·mⱼ (Tᵢ ⊗ Sⱼ)` -/
def tensor_hom {gens : List SchemeOverQ}
    {s₁ t₁ s₂ t₂ : CanonicalWord gens}
    (f : FormalTraceMorphSum gens s₁ t₁)
    (g : FormalTraceMorphSum gens s₂ t₂) :
    FormalTraceMorphSum gens
      (CanonicalWord.tensor s₁ s₂)
      (CanonicalWord.tensor t₁ t₂) :=
  ⟨f.summands.flatMap fun (n, T_f) =>
    g.summands.map fun (m, T_g) => (n * m, T_f.tensor T_g)⟩

end FormalTraceMorphSum

variable (gens : List SchemeOverQ)

/-! ## The canonical trace category -/

/-- The canonical trace category `Tcan(gens)` as a `TraceDoctrine` instance.

    - **Objects**    : `CanonicalWord gens`
    - **Morphisms**  : `FormalTraceMorphSum gens s t`
      (ℤ-linear combinations of `TraceMorphism`; a list presentation)
    - **Identity**   : singleton `[(1, TraceMorphism.id w)]`
    - **Composition**: bilinear extension via `FormalTraceMorphSum.comp`
    - **Tensor**     : strict monoidal via `FormalTraceMorphSum.tensor_hom`
    - **Eval/Coeval**: singleton sums wrapping `TraceMorphism.eval`/`coeval`

    No normalization certificates (`TraceCertificate`) are constructed here.
    The upgrade from `TraceMorphism` to `CertifiedTrace` is deferred to
    `NormalForm.lean`, which provides `isNormal` and `twoCellCoverage` via
    the normalization algorithm. -/
def TcanCategory : TraceDoctrine where
  Obj        := CanonicalWord gens
  Hom        := FormalTraceMorphSum gens
  zero_hom   := .zero
  add_hom    := .add
  neg_hom    := .neg
  id   w     := ⟨[(1, TraceMorphism.ofId w)]⟩
  comp       := FormalTraceMorphSum.comp
  tensor     := CanonicalWord.tensor
  unit       := CanonicalWord.unit
  tate       := CanonicalWord.tate 1
  dual       := CanonicalWord.dual
  tensor_hom := FormalTraceMorphSum.tensor_hom
  eval   w   := ⟨[(1, TraceMorphism.ofEval w)]⟩
  coeval w   := ⟨[(1, TraceMorphism.ofCoeval w)]⟩

/-! ## Laws -/

/-- Laws for `TcanCategory(gens)`.

    Object-level tensor associativity and unit laws are stated here; they are
    SYNTACTIC facts about `CanonicalWord` and hold definitionally once words are
    in canonical form (from `Syntax.lean`'s normalization).

    Morphism-level laws (bilinearity, comp-assoc, etc.) hold in the
    `traceHomSetoid` quotient; they are not propositional equalities on
    `FormalTraceMorphSum` lists without normalization. -/
structure TcanCategoryLaws extends TraceDoctrineLaws (TcanCategory gens) where
  /-- Associativity of tensor on objects. -/
  tensor_assoc      : ∀ (a b c : CanonicalWord gens),
    CanonicalWord.tensor (CanonicalWord.tensor a b) c =
    CanonicalWord.tensor a (CanonicalWord.tensor b c)
  /-- Left unit of tensor on objects. -/
  tensor_unit_left  : ∀ (w : CanonicalWord gens),
    CanonicalWord.tensor CanonicalWord.unit w = w
  /-- Right unit of tensor on objects. -/
  tensor_unit_right : ∀ (w : CanonicalWord gens),
    CanonicalWord.tensor w CanonicalWord.unit = w

/-! ## Geometric data alias -/

end MacLane.Trace
