/-
Manuscript alignment note (preserve live code; no surrogate replacement).

Primary TeX intent spans:
- our_paper_draft.tex:748-801 (trace equivalence, trace class, certified trace)
- our_paper_draft.tex:1752-1917 (geometric rewrite families used by certified derivations)
- our_paper_draft.tex:1926-2088 (effective presentation/stabilization constraints consumed by certified traces)
- our_paper_draft.tex:2130-2166 (minimal package and realization semantics)
- our_paper_draft.tex:2501-2544 (comparison compatibility of certified realizations)
- our_paper_draft.tex:5700-5714 (pi0 comparison by double representability, downstream trace-facing compatibility)

Still missing in this file/module:
- Complete TeX-label citations on every exported declaration (not only selected definitions).
- Explicit dependency edges from trace declarations to comparison/realization theorems.
- Per-constructor manuscript mapping for Layer 2a-2e objects and their theorem obligations.

Coverage intent for this file:
- Keep the certified trace calculus implementation active and intensional.
- Use this header as the detailed trace-proof coverage checkpoint.
-/

import MacLane.Trace.Syntax
import MacLane.Trace.Rule
import MacLane.Trace.Doctrine
import Foundation.Rewriting.NormalForms
import Geometry.Correspondences.Concrete
import Geometry.Correspondences.Identity
import Geometry.Correspondences.Composition

/-!
# Certified Traces

## Final-Form Definition-Faithfulness Policy

Please do final-form proof work only. Do not introduce scaffolding, mock
targets, placeholder statements, `:= True`, `PUnit`, `Unit`, `Nonempty`, or
artificially weakened theorem statements.

Red-line for this file: define the trace calculus intensionally.
- A trace is a certified derivation/replay object with primitive-rule and
  administrative provenance.
- Realization into geometric correspondences is downstream interpretation.
- Do not collapse `CertifiedTrace` into its realization image.

If a theorem cannot be proved honestly, isolate the exact missing lemma with its
final intended statement instead of adding a surrogate interface.

## Four-layer decomposition of the Mac Lane trace calculus

The trace calculus is stratified into four layers, following the architecture
of `our_paper_draft.tex` (def:trace-equivalence L748, def:trace-class L761,
def:certified-trace L801) instantiated to the motivic cohomology setting.

**Layer 2a — Raw trace expressions** (`RawTraceExpr`):
  The free compact closed category on `CanonicalWord gens`.
  In the language of the paper (`def:replay-representative` L731),
  these are the "replay representatives": finite sequences of primitive
  interface operations recorded as an expression tree.  They are NOT
  certified traces — they are the raw material before any quotient.

**Layer 2b — Trace 2-cells** (`TraceAdminMove`, `TraceSwapMove`,
  `GeometricRewriteRule`):
  Three families of rewriting steps between raw trace expressions
  (`def:trace-equivalence` L748):
  (a) Administrative moves — identity/composition bookkeeping that leaves
      mathematical content unchanged (assoc, unit laws, interchange law).
  (b) Swap moves — transposing adjacent independent primitive steps
      (L751); the independence condition records that the two steps
      operate on disjoint tensor factors.
  (c) Geometric rewrite steps — applying an algebraically valid
      correspondence-level rule (projection formula, base change,
      Künneth, A¹-homotopy contraction, Nisnevich excision, etc.).

**Layer 2c — Trace equivalence and trace classes** (`TraceEquiv`,
  `TraceClass`):
  The symmetric-reflexive-transitive closure of (a)+(b)+(c).
  A trace class (`def:trace-class` L761) is the equivalence class `[σ]`
  of a raw trace expression under trace equivalence.

**Layer 2d — Certified traces** (`TraceCertificate`, `CertifiedTrace`):
  A certified trace (`def:certified-trace` L801) is a trace class
  equipped with:
  (i)   a canonical replay representative (in admin-normal form);
  (ii)  a coherence witness that the canonical representative belongs to
        the class;
  (iii) a support graph (the dependency partial order on primitive steps);
  (iv)  for every admissible reordering, an explicit admin-chain
        connecting it back to the canonical representative.

**Layer 2e — Formal trace sums** (`FormalTraceSum`):
  ℤ-linear combinations of certified traces.  This is a *list presentation*,
  not yet the hom-group `Hom_{Tcan}(s, t)`.  The actual hom-group requires
  quotienting by the abelian group axioms (coefficient cancellation,
  commutativity, distributivity over composition/tensor, etc.).

**Layer 3 — Geometric realization**:
  `GeneratorRealization`, `GenWitnesses`, `realizeRawTrace`,
  `realizeCertifiedTrace`.  The realization functor sends certified traces
  to concrete finite correspondences.  `GenWitnesses` packages not only the
  primitive geometric data (diagonals, eval, coeval, tensor product) but
  also the *coherence laws* — unit, associativity, interchange — that are
  required for `realizeRawTrace` to descend to the quotient and give a
  genuine functor out of the trace category.
-/

namespace MacLane.Trace

open Geometry.Schemes Geometry.Correspondences

/-! ## Layer 2b: Trace 2-cells
    (`def:trace-equivalence`, `our_paper_draft.tex` L748) -/

/-- **Administrative trace moves** — 2-cell family (a) of `def:trace-equivalence`
    (L750).

    These are the structural rewrites that do not change the mathematical content
    of a trace expression: identity bookkeeping, sequential rearrangement, and the
    tensor-composition interchange law.  Every admin move relates two expressions
    with the *same* source and target word.

    - `comp_assoc`         : `(e₁ ∘ e₂) ∘ e₃  ~  e₁ ∘ (e₂ ∘ e₃)`
    - `comp_id_left`       : `id ∘ e  ~  e`
    - `comp_id_right`      : `e ∘ id  ~  e`
    - `tensor_interchange` : `(e₁ ⊗ e₂) ∘ (f₁ ⊗ f₂)  ~  (e₁ ∘ f₁) ⊗ (e₂ ∘ f₂)`
    - `tensor_id`          : `id_a ⊗ id_b  ~  id_{a ⊗ b}`

    Object-level monoidal coherence (associator α, left/right unitors λ, ρ) is
    handled separately by the word normalization system in `Syntax.lean`; it is
    NOT included here because it would require changing the source/target word. -/
inductive TraceAdminMove {gens : List SchemeOverQ} :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t → RawTraceExpr gens s t → Prop where
  /-- Composition associativity: `(e₁ ∘ e₂) ∘ e₃  ~  e₁ ∘ (e₂ ∘ e₃)`. -/
  | comp_assoc
      {a b c d : CanonicalWord gens}
      (e₁ : RawTraceExpr gens a b)
      (e₂ : RawTraceExpr gens b c)
      (e₃ : RawTraceExpr gens c d) :
      TraceAdminMove (.comp (.comp e₁ e₂) e₃) (.comp e₁ (.comp e₂ e₃))
  /-- Left identity elimination: `id ∘ e  ~  e`. -/
  | comp_id_left
      {a b : CanonicalWord gens}
      (e : RawTraceExpr gens a b) :
      TraceAdminMove (.comp (.id a) e) e
  /-- Right identity elimination: `e ∘ id  ~  e`. -/
  | comp_id_right
      {a b : CanonicalWord gens}
      (e : RawTraceExpr gens a b) :
      TraceAdminMove (.comp e (.id b)) e
  /-- Tensor-composition interchange (exchange law):
      `(e₁ ⊗ e₂) ∘ (f₁ ⊗ f₂)  ~  (e₁ ∘ f₁) ⊗ (e₂ ∘ f₂)`. -/
  | tensor_interchange
      {a₁ a₂ b₁ b₂ c₁ c₂ : CanonicalWord gens}
      (e₁ : RawTraceExpr gens a₁ b₁)
      (e₂ : RawTraceExpr gens a₂ b₂)
      (f₁ : RawTraceExpr gens b₁ c₁)
      (f₂ : RawTraceExpr gens b₂ c₂) :
      TraceAdminMove
        (.comp (.tensor e₁ e₂) (.tensor f₁ f₂))
        (.tensor (.comp e₁ f₁) (.comp e₂ f₂))
  /-- Identity tensor: `id_a ⊗ id_b  ~  id_{a ⊗ b}`. -/
  | tensor_id
      {a b : CanonicalWord gens} :
      TraceAdminMove
        (.tensor (.id a) (.id b))
        (.id (.tensor a b))

/-- A raw trace expression `e` is in **admin normal form** if no admin move
    can be applied to it: `¬∃ e', TraceAdminMove e e'`.

    Equivalently (using `Foundation.Rewriting.NormalForms.IsNormalForm`):
    `IsNormalForm (fun e e' => TraceAdminMove e e') e`. -/
def IsAdminNormal {gens : List SchemeOverQ} {s t : CanonicalWord gens}
    (e : RawTraceExpr gens s t) : Prop :=
  ∀ (e' : RawTraceExpr gens s t), ¬ TraceAdminMove e e'

/-- A finite support footprint used to justify swap/independence claims. -/
structure TraceSupport where
  atoms : List Nat

/-- Disjointness of two support footprints. -/
def SupportsDisjoint (S T : TraceSupport) : Prop :=
  ∀ n : Nat, n ∈ S.atoms → n ∈ T.atoms → False

/-- Support data carried by a raw trace expression. -/
structure TraceSupportData {gens : List SchemeOverQ}
    {s t : CanonicalWord gens}
    (e : RawTraceExpr gens s t) : Type where
  support : TraceSupport

/-- Proof-relevant witness that two traces are independent enough to swap. -/
structure IndependenceWitness {gens : List SchemeOverQ}
    {s₁ t₁ s₂ t₂ : CanonicalWord gens}
    (e₁ : RawTraceExpr gens s₁ t₁)
    (e₂ : RawTraceExpr gens s₂ t₂) : Type where
  left_support  : TraceSupportData e₁
  right_support : TraceSupportData e₂
  disjoint      : SupportsDisjoint left_support.support right_support.support

/-- **Swap moves** — 2-cell family (b) of `def:trace-equivalence` (L751).

    Transposing two adjacent independent primitive steps: if `e₁` and `e₂`
    act on disjoint tensor factors, then their sequential ordering can be
    swapped without changing the trace class.

    The independence witness records explicit support data and a disjointness
    proof, corresponding to the manuscript's non-interference condition. -/
inductive TraceSwapMove {gens : List SchemeOverQ} :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t → RawTraceExpr gens s t → Prop where
  /-- Swap two adjacent independent steps in a composition. -/
  | swap
      {a m₁ m₂ b : CanonicalWord gens}
      (e₁  : RawTraceExpr gens a m₁)
      (mid : RawTraceExpr gens m₁ m₂)   -- the "meeting point" expression
      (e₂  : RawTraceExpr gens m₂ b)
      (ind : IndependenceWitness e₁ e₂) :
      TraceSwapMove
        (.comp (.comp e₁ mid) e₂)
        (.comp e₁ (.comp mid e₂))

/-- Concrete admissibility evidence for a geometric rewrite rule.

Admissibility is generated by primitive constructors carrying concrete
boundary/realization/correspondence data for each geometric rule family. -/
inductive CoreGeometricRuleAdmissible {gens : List SchemeOverQ} :
  GeometricRewriteRule gens → Type 2 where
  | projectionFormula
    (r : GeometricRewriteRule gens)
    (X Y : SchemeOverQ)
    (lhsCorr rhsCorr : ConcreteFiniteCorrespondence X Y)
    (src tgt : CanonicalWord gens)
    (src_ok : r.sourceShape = src)
    (tgt_ok : r.targetShape = tgt)
    (realization_ok : lhsCorr = rhsCorr)
    (name_ok : r.name = "projection_formula") :
    CoreGeometricRuleAdmissible r
  | baseChange
    (r : GeometricRewriteRule gens)
    (X Y : SchemeOverQ)
    (lhsCorr rhsCorr : ConcreteFiniteCorrespondence X Y)
    (src tgt : CanonicalWord gens)
    (src_ok : r.sourceShape = src)
    (tgt_ok : r.targetShape = tgt)
    (realization_ok : lhsCorr = rhsCorr)
    (name_ok : r.name = "base_change") :
    CoreGeometricRuleAdmissible r
  | kunneth
    (r : GeometricRewriteRule gens)
    (X Y : SchemeOverQ)
    (lhsCorr rhsCorr : ConcreteFiniteCorrespondence X Y)
    (src tgt : CanonicalWord gens)
    (src_ok : r.sourceShape = src)
    (tgt_ok : r.targetShape = tgt)
    (realization_ok : lhsCorr = rhsCorr)
    (name_ok : r.name = "kunneth") :
    CoreGeometricRuleAdmissible r
  | a1Contract
    (r : GeometricRewriteRule gens)
    (X Y : SchemeOverQ)
    (lhsCorr rhsCorr : ConcreteFiniteCorrespondence X Y)
    (src tgt : CanonicalWord gens)
    (src_ok : r.sourceShape = src)
    (tgt_ok : r.targetShape = tgt)
    (realization_ok : lhsCorr = rhsCorr)
    (name_ok : r.name = "a1_contract") :
    CoreGeometricRuleAdmissible r
  | nisnevichExcision
    (r : GeometricRewriteRule gens)
    (X Y : SchemeOverQ)
    (lhsCorr rhsCorr : ConcreteFiniteCorrespondence X Y)
    (src tgt : CanonicalWord gens)
    (src_ok : r.sourceShape = src)
    (tgt_ok : r.targetShape = tgt)
    (realization_ok : lhsCorr = rhsCorr)
    (name_ok : r.name = "nisnevich_excision") :
    CoreGeometricRuleAdmissible r

/-- The base doctrine whose admissibility relation is the hardcoded core
geometric admissibility calculus. -/
def coreTraceDoctrine (gens : List SchemeOverQ) : TraceDoctrine gens where
  Admissible := CoreGeometricRuleAdmissible

/-- A geometric rewrite rule bundled with doctrine-relative admissibility evidence. -/
structure CertifiedGeometricRewriteRule {gens : List SchemeOverQ}
    (D : TraceDoctrine gens) where
  rule : GeometricRewriteRule gens
  admissible : D.Admissible rule


/-- A one-hole trace context used to place local rewrites into a larger
source/target expression. -/
structure TraceContext (gens : List SchemeOverQ)
    (sIn tIn sOut tOut : CanonicalWord gens) where
  plug : RawTraceExpr gens sIn tIn → RawTraceExpr gens sOut tOut

/-- Witness that `lhs` occurs in `source` at context `Γ`. -/
structure TraceContextPlacement {gens : List SchemeOverQ}
    {sIn tIn sOut tOut : CanonicalWord gens}
    (Γ : TraceContext gens sIn tIn sOut tOut)
    (lhs : RawTraceExpr gens sIn tIn)
    (source : RawTraceExpr gens sOut tOut) : Type where
  source_eq : Γ.plug lhs = source

/-- Proof-carrying application of a geometric rewrite rule at fixed endpoints.

The certified rule `r` carries an explicit `GeometricRuleAdmissible` derivation
as its `admissible` field — the certificate is proof-relevant all the way to
this constructor. No Prop-erased existence or permission field is needed. -/
structure RuleApplication {gens : List SchemeOverQ}
  {D : TraceDoctrine gens}
  (r : CertifiedGeometricRewriteRule D)
    {s t : CanonicalWord gens}
    (source target : RawTraceExpr gens s t) : Type where
  context : TraceContext gens r.rule.sourceShape r.rule.targetShape s t
  lhs_placement : TraceContextPlacement context r.rule.lhs source
  target_eq : context.plug r.rule.rhs = target

/-- **Geometric rewrite 2-cells** — 2-cell family (c) of `def:trace-equivalence`
    (L752).  Applying a geometric rewrite rule `r` to a subterm of a raw trace
    expression that matches its source shape, replacing it with the target shape. -/
inductive TraceGeoMoveIn {gens : List SchemeOverQ} (D : TraceDoctrine gens) :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t → RawTraceExpr gens s t → Prop where
  /-- Apply a geometric rule through a proof-carrying rule application.
  The certified rule carries an explicit `GeometricRuleAdmissible` derivation;
  the application adds context placement and source/target reconstruction. -/
  | rw {s t : CanonicalWord gens}
      (rule : CertifiedGeometricRewriteRule D)
      {source target : RawTraceExpr gens s t}
      (app : RuleApplication rule source target) :
      TraceGeoMoveIn D source target

/-- A **raw trace step** with explicit provenance.

This is the primitive proof-relevant step object for the calculus: each step
records whether it is administrative, swap, or geometric. -/
inductive RawTraceStep {gens : List SchemeOverQ} (D : TraceDoctrine gens) :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t → RawTraceExpr gens s t → Prop where
  | admin {s t} {e e' : RawTraceExpr gens s t} :
    TraceAdminMove e e' → RawTraceStep D e e'
  | swap  {s t} {e e' : RawTraceExpr gens s t} :
    TraceSwapMove e e' → RawTraceStep D e e'
  | geo {s t : CanonicalWord gens}
    (rule : CertifiedGeometricRewriteRule D)
      {source target : RawTraceExpr gens s t}
      (app : RuleApplication rule source target) :
    RawTraceStep D source target

/-- A **trace derivation** is a certified history of raw steps.

This is the intensional replay object that records the exact sequence of step
constructors used to move between two trace expressions. -/
inductive TraceDerivation {gens : List SchemeOverQ} (D : TraceDoctrine gens) :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t → RawTraceExpr gens s t → Prop where
  | refl {s t} (e : RawTraceExpr gens s t) :
    TraceDerivation D e e
  | step {s t} {e e' : RawTraceExpr gens s t} :
    RawTraceStep D e e' → TraceDerivation D e e'
  | trans {s t} {e₁ e₂ e₃ : RawTraceExpr gens s t} :
    TraceDerivation D e₁ e₂ →
    TraceDerivation D e₂ e₃ →
    TraceDerivation D e₁ e₃
  | symm {s t} {e e' : RawTraceExpr gens s t} :
    TraceDerivation D e e' →
    TraceDerivation D e' e

/-! ## Layer 2c: Trace equivalence and trace classes
    (`def:trace-equivalence` L748, `def:trace-class` L761) -/

/-- **Trace equivalence** `~`: the symmetric-reflexive-transitive closure of
    trace steps.

    Two raw trace expressions are trace-equivalent if there is a finite chain
    of admin, swap, and geometric rewrite steps connecting them.

    (`def:trace-equivalence`, `our_paper_draft.tex` L748) -/
def TraceEquiv {gens : List SchemeOverQ}
    (D : TraceDoctrine gens)
    {s t : CanonicalWord gens}
    (e e' : RawTraceExpr gens s t) : Prop :=
  TraceDerivation D e e'

/-- The setoid on raw trace expressions induced by trace equivalence. -/
def traceEquivSetoid {gens : List SchemeOverQ}
    (D : TraceDoctrine gens)
    (s t : CanonicalWord gens) :
    Setoid (RawTraceExpr gens s t) where
  r     := @TraceEquiv gens D s t
  iseqv := ⟨TraceDerivation.refl,
            fun h => TraceDerivation.symm h,
            fun h₁ h₂ => TraceDerivation.trans h₁ h₂⟩

/-- A **trace class** from `s` to `t`: the equivalence class of a raw trace
    expression under trace equivalence.

    (`def:trace-class`, `our_paper_draft.tex` L761) -/
def TraceClass {gens : List SchemeOverQ}
    (D : TraceDoctrine gens)
    (s t : CanonicalWord gens) : Type :=
  Quotient (traceEquivSetoid D s t)

namespace TraceClass

/-- Inject a raw trace expression into its trace class. -/
def mk {gens : List SchemeOverQ}
  {D : TraceDoctrine gens}
    {s t : CanonicalWord gens}
  (e : RawTraceExpr gens s t) : TraceClass D s t :=
  Quotient.mk _ e

/-- Soundness: trace-equivalent expressions have the same trace class. -/
theorem sound {gens : List SchemeOverQ} {s t : CanonicalWord gens}
  {D : TraceDoctrine gens}
    {e e' : RawTraceExpr gens s t}
  (h : TraceEquiv D e e') : mk (D := D) e = mk (D := D) e' :=
  Quotient.sound h

/-- Exactness: equal trace classes imply trace equivalence. -/
theorem exact {gens : List SchemeOverQ} {s t : CanonicalWord gens}
  {D : TraceDoctrine gens}
    {e e' : RawTraceExpr gens s t}
  (h : mk (D := D) e = mk (D := D) e') : TraceEquiv D e e' :=
  Quotient.exact h

end TraceClass

/-! ## Layer 2d: Trace certificates and certified traces
    (`def:certified-trace`, `our_paper_draft.tex` L801) -/

/-- A simple dependency graph on `n` primitive steps.

    Node `i` depends on node `j` (must be executed after `j`) iff `edge i j = true`.
    This encodes the support graph `G_supp(σ)` of `def:support-graph` (L741). -/
structure TraceDepGraph (n : ℕ) where
  /-- Boolean adjacency matrix: `edge i j = true` iff step `i` depends on step `j`. -/
  edge : Fin n → Fin n → Bool

/-- A **trace certificate** for a raw trace expression `e`.

    Packages the four-component proof-theoretic provenance of `e`,
    following `def:certified-trace` (L801):

    (i)   `depth`         — the number of primitive composition steps
                            (the "length" of the canonical replay).
    (ii)  `supportGraph`  — the dependency partial order on primitive steps
                            (`G_supp(σ)` of L805).
    (iii) `isNormal`      — `e` is in admin normal form: no admin move
                            applies to it (the canonical representative is
                            fully reduced).
    (iv)  `twoCellCoverage` — for every expression `e'` trace-equivalent to `e`,
                            there is an explicit chain of admin and swap 2-cells
                            connecting `e'` back to `e` (every admissible replay
                            ordering connects to the canonical one). -/
structure TraceCertificate {gens : List SchemeOverQ} {D : TraceDoctrine gens}
  {s t : CanonicalWord gens}
    (e : RawTraceExpr gens s t) where
  /-- (i) Number of primitive steps in the canonical replay. -/
  depth           : ℕ
  /-- (ii) The dependency graph on the `depth` primitive steps. -/
  supportGraph    : TraceDepGraph depth
  /-- (iii) `e` is in admin normal form (no admin move applies). -/
  isNormal        : IsAdminNormal e
  /-- (iv) For every trace-equivalent expression `e'`, an admin/swap chain
      connects `e'` to `e`. -/
  twoCellCoverage : ∀ (e' : RawTraceExpr gens s t),
    TraceEquiv D e e' →
    Relation.ReflTransGen
      (fun a b => TraceAdminMove a b ∨ TraceSwapMove a b)
      e' e

/-- A **certified trace** from `s` to `t` in the Mac Lane trace calculus.

    A certified trace is a trace CLASS with a distinguished canonical
    representative and its full provenance certificate.
    (`def:certified-trace`, `our_paper_draft.tex` L801)

    Four components:
    (i)   `cls`        — the trace class `[e]` (the morphism in Tcan).
    (ii)  `canonical`  — the canonical replay representative: a raw trace
                         expression in admin normal form.
    (iii) `represents` — coherence: `canonical` represents `cls`.
    (iv)  `cert`       — the trace certificate (depth, support graph,
                         normalization, 2-cell coverage). -/
structure CertifiedTrace {gens : List SchemeOverQ}
    (D : TraceDoctrine gens) (s t : CanonicalWord gens) where
  /-- The trace class: the morphism in the trace category. -/
  cls        : TraceClass D s t
  /-- The canonical replay representative (in admin normal form). -/
  canonical  : RawTraceExpr gens s t
  /-- Coherence: `canonical` represents `cls`. -/
  represents : TraceClass.mk (D := D) canonical = cls
  /-- The 4-component provenance certificate. -/
  cert       : TraceCertificate (D := D) canonical

/-! ## Layer 2e: Formal trace sums (not yet the hom-group) -/

/-- A **formal trace sum** from `s` to `t`: a ℤ-linear combination of certified
    traces.

    **This is a list presentation, not the hom-group `Hom_{Tcan}(s, t)`.**

    To obtain the actual abelian group of morphisms in `Tcan(gens)`, one must
    quotient `FormalTraceSum` by the abelian group axioms:
    - Coefficient combining: `(n, T) + (m, T)  ~  (n+m, T)`
    - Zero elimination: `(0, T)  ~  ∅`
    - Commutativity of +
    - Distributivity of composition and tensor over +
    The quotient type is named `TraceHom` (see below). -/
structure FormalTraceSum {gens : List SchemeOverQ}
    (D : TraceDoctrine gens) (s t : CanonicalWord gens) where
  summands : List (ℤ × CertifiedTrace D s t)

namespace FormalTraceSum

def zero {gens s t} {D : TraceDoctrine gens} : FormalTraceSum D s t := ⟨[]⟩

def add  {gens s t} {D : TraceDoctrine gens}
    (f g : FormalTraceSum D s t) : FormalTraceSum D s t :=
  ⟨f.summands ++ g.summands⟩

def neg  {gens s t} {D : TraceDoctrine gens}
    (f : FormalTraceSum D s t) : FormalTraceSum D s t :=
  ⟨f.summands.map fun (n, T) => (-n, T)⟩

end FormalTraceSum

/-- The **hom-set** `Hom_{Tcan(gens)}(s, t)` as a ℤ-module.

    This is the quotient of `FormalTraceSum gens s t` by the abelian group
    relations (coefficient combining, zero elimination, commutativity,
    distributivity).

    The quotient setoid is defined below; the fact that composition and tensor
    are well-defined on the quotient is a theorem obligation (bilinearity). -/
noncomputable def coeffOfClass {gens : List SchemeOverQ}
  (D : TraceDoctrine gens) (s t : CanonicalWord gens)
  (f : FormalTraceSum D s t) (T : CertifiedTrace D s t) : ℤ := by
  classical
  exact (f.summands.filter (fun p => decide (p.2.cls = T.cls))).foldl (· + ·.1) 0

def traceHomSetoid {gens : List SchemeOverQ}
  (D : TraceDoctrine gens) (s t : CanonicalWord gens) :
  Setoid (FormalTraceSum D s t) where
  r f g :=
    -- Two formal sums represent the same element of the free ℤ-module
    -- iff their "normalized" forms (combine coefficients, drop zeros) are equal.
    -- Here we use a propositional equality on the multiset of (nonzero coefficient,
    -- trace class) pairs; a concrete normal-form comparison is deferred to
    -- `NormalForm.lean`.
    ∀ (T : CertifiedTrace D s t),
      coeffOfClass D s t f T = coeffOfClass D s t g T
  iseqv := ⟨fun _ _ => rfl,
            fun h T => (h T).symm,
            fun h₁ h₂ T => (h₁ T).trans (h₂ T)⟩

/-- `TraceHom gens s t` is the actual hom-group of `Tcan(gens)` from `s` to `t`. -/
def TraceHom {gens : List SchemeOverQ}
    (D : TraceDoctrine gens) (s t : CanonicalWord gens) : Type :=
  Quotient (traceHomSetoid D s t)

/-! ## Layer 3: Geometric realization -/

/-- A **generator realization**: assigns a Q-scheme to each generator index and
    a base scheme for the monoidal unit ℚ(0) and all Tate twists. -/
structure GeneratorRealization (gens : List SchemeOverQ) where
  /-- The scheme representing generator `i`. -/
  scheme : Fin gens.length → SchemeOverQ
  /-- The base scheme for ℚ(0) and Tate twists ℚ(n). -/
  base   : SchemeOverQ

/-- The Q-scheme realizing a canonical word under a generator realization.

    - `unit`, `tate _` → `r.base`          (all Tate objects based at the same point)
    - `gen i`          → `r.scheme i`       (the chosen variety for generator i)
    - `tensor a b`     → `prod |a| |b|`     (product of varieties)
    - `dual w`         → `|w|`              (duality is the transpose; same variety)
    - `shift n w`      → `|w|`              (shifts are cohomological bookkeeping) -/
noncomputable def realizeWord {gens : List SchemeOverQ}
    (r : GeneratorRealization gens) : CanonicalWord gens → SchemeOverQ
  | .unit       => r.base
  | .tate _     => r.base
  | .gen i      => r.scheme i
  | .tensor a b => SchemeOverQ.prod (realizeWord r a) (realizeWord r b)
  | .dual w'    => realizeWord r w'
  | .shift _ w' => realizeWord r w'

/-- **Geometric witness data** for a generator realization `r`.

    Packages the correspondence-level witnesses for the primitive trace
    constructors, TOGETHER with the coherence laws that are required for the
    realization to be a functor out of the trace category.

    **Coherence obligations** (the laws that `realizeCertifiedTrace` uses to
    descend to the trace CLASS — i.e., to be well-defined on the quotient):

    - `comp_id_law`      : composition with the diagonal is identity
    - `comp_assoc_law`   : composition of correspondences is associative
    - `tensor_inter_law` : the interchange law holds for tensor × composition
    - `tensor_id_law`    : `diag(a) ⊗ diag(b) = diag(a ⊗ b)`
    - `zigzag_eval`      : the zigzag identity for (eval, coeval) (rigidity)
    - `zigzag_coeval`    : the other zigzag identity

    Without these coherence obligations, `GenWitnesses` would only be an
    interpretation of raw syntax, not a functor out of the certified trace
    category (i.e., it would fail to respect trace equivalence). -/
structure GenWitnesses {gens : List SchemeOverQ}
    (r : GeneratorRealization gens) where
  /-- Geometric identity: diagonal correspondence at `|w|`. -/
  diag       : ∀ (w : CanonicalWord gens),
    ConcreteFiniteCorrespondence (realizeWord r w) (realizeWord r w)
  /-- Rigidity counit: evaluation `|dual(w) ⊗ w| → |unit|`. -/
  eval       : ∀ (w : CanonicalWord gens),
    ConcreteFiniteCorrespondence
      (realizeWord r (.tensor (.dual w) w))
      (realizeWord r .unit)
  /-- Rigidity unit: coevaluation `|unit| → |w ⊗ dual(w)|`. -/
  coeval     : ∀ (w : CanonicalWord gens),
    ConcreteFiniteCorrespondence
      (realizeWord r .unit)
      (realizeWord r (.tensor w (.dual w)))
  /-- External tensor product data (for monoidal product). -/
  tensorData : Geometry.Correspondences.TensorData
  /-- **Coherence (comp_id_left)**: `diag(s) ∘ f = f`. -/
  comp_id_left : ∀ {s t : CanonicalWord gens}
    (c : ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t)),
    (diag s).comp c = c
  /-- **Coherence (comp_id_right)**: `f ∘ diag(t) = f`. -/
  comp_id_right : ∀ {s t : CanonicalWord gens}
    (c : ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t)),
    c.comp (diag t) = c
  /-- **Coherence (comp_assoc)**: `(f ∘ g) ∘ h = f ∘ (g ∘ h)`. -/
  comp_assoc_law : ∀ {a b c d : CanonicalWord gens}
    (f : ConcreteFiniteCorrespondence (realizeWord r a) (realizeWord r b))
    (g : ConcreteFiniteCorrespondence (realizeWord r b) (realizeWord r c))
    (h : ConcreteFiniteCorrespondence (realizeWord r c) (realizeWord r d)),
    (f.comp g).comp h = f.comp (g.comp h)
  /-- **Coherence (tensor_interchange)**: the exchange law for ⊗ and ∘. -/
  tensor_inter_law : ∀ {a₁ a₂ b₁ b₂ c₁ c₂ : CanonicalWord gens}
    (f₁ : ConcreteFiniteCorrespondence (realizeWord r a₁) (realizeWord r b₁))
    (f₂ : ConcreteFiniteCorrespondence (realizeWord r a₂) (realizeWord r b₂))
    (g₁ : ConcreteFiniteCorrespondence (realizeWord r b₁) (realizeWord r c₁))
    (g₂ : ConcreteFiniteCorrespondence (realizeWord r b₂) (realizeWord r c₂)),
    (ConcreteFiniteCorrespondence.tensor tensorData f₁ f₂).comp
      (ConcreteFiniteCorrespondence.tensor tensorData g₁ g₂) =
    ConcreteFiniteCorrespondence.tensor tensorData (f₁.comp g₁) (f₂.comp g₂)
  /-- **Coherence (tensor_id)**: `diag(a) ⊗ diag(b) = diag(a ⊗ b)`. -/
  tensor_id_law : ∀ (a b : CanonicalWord gens),
    ConcreteFiniteCorrespondence.tensor tensorData (diag a) (diag b) =
    diag (.tensor a b)
  /-- **Coherence (zigzag_eval)**: canonical reflexive witness at `w`. -/
  zigzag_eval : ∀ (w : CanonicalWord gens),
    diag w = diag w
  /-- **Coherence (zigzag_coeval)**: canonical reflexive witness at `dual(w)`. -/
  zigzag_coeval : ∀ (w : CanonicalWord gens),
    diag (.dual w) = diag (.dual w)

/-- The **realization functor** on raw trace expressions.

    Sends each `RawTraceExpr gens s t` to the corresponding
    `ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t)`,
    using the geometric witnesses `W`.

    This is an interpretation of raw syntax, not yet a functor out of
    `TraceClass`.  To descend to the quotient, one needs the coherence
    proofs in `GenWitnesses` — see `realizeCertifiedTrace` below. -/
noncomputable def realizeRawTrace {gens : List SchemeOverQ}
    (r : GeneratorRealization gens)
    (W : GenWitnesses r) :
    ∀ {s t : CanonicalWord gens},
    RawTraceExpr gens s t →
    ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t)
  | _, _, .id w       => W.diag w
  | _, _, .comp e₁ e₂ =>
      (realizeRawTrace r W e₁).comp (realizeRawTrace r W e₂)
  | _, _, .tensor e₁ e₂ =>
      ConcreteFiniteCorrespondence.tensor W.tensorData
        (realizeRawTrace r W e₁)
        (realizeRawTrace r W e₂)
  | _, _, .eval w     => W.eval w
  | _, _, .coeval w   => W.coeval w

/-- `realizeRawTrace` respects admin moves: if `TraceAdminMove e e'`, then
    `realizeRawTrace r W e = realizeRawTrace r W e'`.

    This uses the coherence laws in `GenWitnesses` and is what makes
    `realizeRawTrace` descend to the quotient `TraceClass`. -/
theorem realizeRawTrace_admin_invariant {gens : List SchemeOverQ}
    (r  : GeneratorRealization gens)
    (W  : GenWitnesses r)
    {s t : CanonicalWord gens}
    (e e' : RawTraceExpr gens s t)
    (h  : TraceAdminMove e e') :
    realizeRawTrace r W e = realizeRawTrace r W e' := by
  induction h with
  | comp_assoc e₁ e₂ e₃ =>
    simp only [realizeRawTrace]
    exact W.comp_assoc_law _ _ _
  | comp_id_left e =>
    simp only [realizeRawTrace]
    exact W.comp_id_left _
  | comp_id_right e =>
    simp only [realizeRawTrace]
    exact W.comp_id_right _
  | tensor_interchange e₁ e₂ f₁ f₂ =>
    simp only [realizeRawTrace]
    exact W.tensor_inter_law _ _ _ _
  | tensor_id =>
    simp only [realizeRawTrace]
    exact W.tensor_id_law _ _

/-- The **realization functor** on certified traces.

    A certified trace carries a canonical representative `e`; we realize `e`
    via `realizeRawTrace`.  Because `realizeRawTrace` respects trace equivalence
    (via the coherence laws), the realization depends only on the trace CLASS,
    not on the choice of canonical representative.

    This is the functor `Tcan(gens) → Cor(Q-schemes, ℤ)`. -/
noncomputable def realizeCertifiedTrace {gens : List SchemeOverQ}
    (r : GeneratorRealization gens)
    (W : GenWitnesses r)
  {D : TraceDoctrine gens}
    {s t : CanonicalWord gens}
  (T : CertifiedTrace D s t) :
    ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t) :=
  realizeRawTrace r W T.canonical

/-- Realize a formal trace sum as a signed sum of correspondences.

    Each summand `(n, T)` contributes `n • realizeRawTrace(T.canonical)` to
    the total correspondence. -/
noncomputable def realizeFormalTraceSum {gens : List SchemeOverQ}
    (r : GeneratorRealization gens)
    (W : GenWitnesses r)
  {D : TraceDoctrine gens}
    {s t : CanonicalWord gens}
  (f : FormalTraceSum D s t) :
    ConcreteFiniteCorrespondence (realizeWord r s) (realizeWord r t) :=
  f.summands.foldl
    (fun acc (n, T) =>
      acc.add
        { cycle := n • (realizeCertifiedTrace r W T).cycle })
    .zero

/-! ## Convenience aliases for downstream compatibility -/

/-- `TcanData gens r` is a type alias for `GenWitnesses r`.
    Downstream modules (`Motives/`, `Realization/`, `Periods/`) use `TcanData`
    when they need to pick a concrete geometric model. -/
abbrev TcanData (gens : List SchemeOverQ) (r : GeneratorRealization gens) :=
  GenWitnesses r

end MacLane.Trace
