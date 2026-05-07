import TraceCalc.LayerB.RealObjects.ContextualAdminEquiv

/-!
# Real-objects formalization: canonical frontier word descent (items 5n–5q)

**Phase 3B items 5n–5q (2026-04-24).** This file lifts the
administrative-confluence skeleton from item 5l
(`FrontierObservation`) into a manuscript-facing **canonical frontier
word** layer and proves that this word descends through
`ContextualAdminMove` / `ContextualAdminEquiv` modulo
`BoundaryAdminEquiv`.

## Items in this file

* **5n** — `FrontierWord setup` skeletal structure +
  `FrontierObservation.toWord` + `canonicalFrontierWord`. **Skeletal
  scope (per stop condition)**: `FrontierWord` packages the truncated
  residue record itself; no normalization machinery is asserted, no
  uniqueness claim is made. This is the *interface object* that future
  CanNF (canonical normal form) work will refine.
* **5o** — `FrontierWord.Equiv` = `RecordStructEquiv BoundaryAdminEquiv`
  lifted to words; `contextual_admin_move_word_stable` and
  `contextual_admin_equiv_word_stable` (descent through items 5h / 5i
  via `toWord`).
* **5p** — `BoundaryAdminEquiv` "generated closure" cleanup. The
  underlying inductive (in `SwapSquare.lean`) already makes
  "`BoundaryAdminEquiv` is the closure of `BoundaryTwoStepSwap`"
  *tautological* via the `ofTwoStepSwap` constructor; per the stop
  condition we only re-export clean aliases / a recursor pointer
  expressing this — no fake substance.
* **5q** — Three manuscript-facing theorem aliases.

## Global invariants honored

* `INV AdminMove-Nonvacuity`: the descent theorems of 5o are direct
  re-packagings of items 5h / 5i, so they ultimately route through
  `peelSink_swap_structEquiv_admin`. NO route through
  `replay_recordEquiv` / `replay_stable`.
* `INV Build-Trust-Gate`: this batch was validated by full `lake build`
  before status sync.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — canonicality
  clause: this file delivers the manuscript phrase
  *"adjacent independent administrative reorderings preserve the
  observed frontier modulo generated boundary administration"* in the
  precise form **`FrontierWord` modulo `FrontierWord.Equiv`**.
* L1186–L1192 — descent through the per-step administrative chain.
* L1224 (`def:boundary-exposure`) — the per-step boundary exposure
  whose generated closure is the right-hand side of the descent.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 5n — Canonical frontier word skeleton -/

/-- **Skeletal canonical frontier word.**

Per the user's verbatim 5n stop condition: *"Keep it skeletal if
needed: it may initially contain just the frontier residue plus its
boundary/admin observation data."*

Concretely, a `FrontierWord setup` packages the **truncated residue
record** observed at some frontier depth. No normalization machinery
is asserted; this is the manuscript-level *interface object* that
future canonical-normal-form work will refine.

This is intentionally **not** a quotient by `BoundaryAdminEquiv`:
descent is recorded as the relation `FrontierWord.Equiv` (item 5o),
not as definitional equality. -/
structure FrontierWord (setup : RewriteCalculusSetup.{u}) where
  /-- The truncated residue record observed at the frontier. -/
  residue : CompletedReconstructionRecord setup

namespace FrontierWord

/-- **Reflexive constructor**: bundle a bare residue as a
`FrontierWord`. -/
@[reducible] def ofResidue (R : CompletedReconstructionRecord setup) :
    FrontierWord setup := ⟨R⟩

@[simp] theorem ofResidue_residue (R : CompletedReconstructionRecord setup) :
    (ofResidue R).residue = R :=
  rfl

@[ext] theorem ext {w₁ w₂ : FrontierWord setup}
    (h : w₁.residue = w₂.residue) : w₁ = w₂ := by
  cases w₁
  cases w₂
  cases h
  rfl

end FrontierWord

namespace PeelChain
namespace FrontierObservation

/-- **Item 5n: `FrontierObservation.toWord`.**

Forget the depth-bookkeeping coherence and keep the observed residue
as a `FrontierWord`. This is the canonical bridge from per-chain
observations to the depth-erased canonical-word layer. -/
def toWord {R : CompletedReconstructionRecord setup}
    {c : PeelChain R} (o : FrontierObservation c) :
    FrontierWord setup :=
  FrontierWord.ofResidue o.residue

@[simp] theorem toWord_residue {R : CompletedReconstructionRecord setup}
    {c : PeelChain R} (o : FrontierObservation c) :
    o.toWord.residue = o.residue := rfl

@[simp] theorem ofChain_toWord_residue
    {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (d : Nat) :
    (FrontierObservation.ofChain c d).toWord.residue
      = residueAt c (d + 2) := rfl

end FrontierObservation
end PeelChain

/-- **Item 5n: `canonicalFrontierWord`.**

Manuscript-facing canonical bundling: from any
`FrontierObservation c`, extract the canonical frontier word. By
construction this is just `toWord` — the alias exists for naming
parity with the manuscript. -/
def canonicalFrontierWord
    {R : CompletedReconstructionRecord setup} {c : PeelChain R}
    (o : PeelChain.FrontierObservation c) : FrontierWord setup :=
  o.toWord

@[simp] theorem canonicalFrontierWord_residue
    {R : CompletedReconstructionRecord setup} {c : PeelChain R}
    (o : PeelChain.FrontierObservation c) :
    (canonicalFrontierWord o).residue = o.residue := rfl

/-! ## Item 5o — Descent through contextual admin equivalence -/

namespace FrontierWord

/-- **Equivalence on canonical frontier words.**

Two words are equivalent when their residue records are
`RecordStructEquiv` along `BoundaryAdminEquiv`. Per the manuscript:
*canonicality is modulo the generated boundary administration*, not
strict equality. -/
def Equiv (w₁ w₂ : FrontierWord setup) : Prop :=
  RecordStructEquiv (@BoundaryAdminEquiv setup) w₁.residue w₂.residue

theorem equiv_of_residue_structEquiv {w₁ w₂ : FrontierWord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) w₁.residue w₂.residue) :
    Equiv w₁ w₂ :=
  h

theorem residue_structEquiv_of_equiv {w₁ w₂ : FrontierWord setup}
    (h : Equiv w₁ w₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup) w₁.residue w₂.residue :=
  h

theorem equiv_iff_residue_structEquiv (w₁ w₂ : FrontierWord setup) :
    Equiv w₁ w₂ ↔ RecordStructEquiv (@BoundaryAdminEquiv setup) w₁.residue w₂.residue :=
  Iff.rfl

namespace Equiv

/-- Reflexivity of `FrontierWord.Equiv`. -/
@[refl] theorem refl (w : FrontierWord setup) : Equiv w w :=
  RecordStructEquiv.refl (fun Y => BoundaryAdminEquiv.refl Y) _

/-- Symmetry of `FrontierWord.Equiv`. -/
@[symm] theorem symm {w₁ w₂ : FrontierWord setup} (h : Equiv w₁ w₂) :
    Equiv w₂ w₁ :=
  RecordStructEquiv.symm (fun hY => hY.symm) h

/-- Transitivity of `FrontierWord.Equiv`. -/
theorem trans {w₁ w₂ w₃ : FrontierWord setup}
    (h₁ : Equiv w₁ w₂) (h₂ : Equiv w₂ w₃) : Equiv w₁ w₃ :=
  RecordStructEquiv.trans (fun hY₁ hY₂ => hY₁.trans hY₂) h₁ h₂

end Equiv

end FrontierWord

namespace PeelChain

/-! ### Descent theorems (5o.5) -/

/-- **Item 5o: `contextual_admin_move_word_stable`.**

A contextual admin move at depth `d` produces canonical frontier
words (at depth `d`) related by `FrontierWord.Equiv`.

**Routing**: `FrontierObservation.ofContextualAdminMove` (item 5l) →
`ContextualAdminMove.residueAt_structEquiv_admin` (item 5h) →
`peelSink_swap_structEquiv_admin` (item 5e-ii). NO replay routing. -/
theorem contextual_admin_move_word_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    FrontierWord.Equiv
      (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  (FrontierObservation.ofContextualAdminMove m).residue_struct_equiv

/-- **Item 5o: `contextual_admin_equiv_word_stable`.**

The closure-lifted descent: a `ContextualAdminEquiv` at depth `d`
produces canonical frontier words related by `FrontierWord.Equiv`.

**Routing**: `FrontierObservation.ofContextualAdminEquiv` (item 5l) →
`ContextualAdminEquiv.residueAt_structEquiv_admin` (item 5i), whose
`ofMove` case is `contextual_admin_move_word_stable` above. -/
theorem contextual_admin_equiv_word_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    FrontierWord.Equiv
      (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  (FrontierObservation.ofContextualAdminEquiv h).residue_struct_equiv

end PeelChain

/-! ## Item 5p — `BoundaryAdminEquiv` generated-closure cleanup

The inductive `BoundaryAdminEquiv` (in `SwapSquare.lean`) is *by
construction* the free equivalence relation generated by
`BoundaryTwoStepSwap`: its constructors are exactly
`refl`/`symm`/`trans`/`ofTwoStepSwap`. The "generated by two-step
swaps" claim is therefore tautological at the inductive level.

Per the user's verbatim 5p stop condition: *"If the current inductive
already makes this tautological, add only clean aliases/eliminators,
not fake substance."* The aliases below name the generator and the
generic recursion principle in manuscript-facing form; they add **no**
mathematical content. -/

namespace BoundaryAdminEquiv

/-- **Item 5p: generator alias.**

Manuscript-facing name for the `ofTwoStepSwap` constructor: a single
local two-step independent-sink swap is admin-equivalent to the
identity it modifies. -/
theorem ofGenerator
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    {h : IndependentSinks R s t}
    {Y₁ Y₂ : setup.BoundaryObject}
    (hSwap : BoundaryTwoStepSwap h Y₁ Y₂) :
    @BoundaryAdminEquiv setup Y₁ Y₂ :=
  BoundaryAdminEquiv.ofTwoStepSwap hSwap

/-- **Item 5p: generated-closure recursion alias.**

A function on `BoundaryAdminEquiv` is determined by its values on the
generator (`BoundaryTwoStepSwap`) together with the equivalence-relation
data. This alias just re-exposes Lean's auto-generated `rec` under a
manuscript-friendly name; it asserts nothing new beyond the inductive
definition.

The motive `P` is allowed to depend on the equivalence proof itself
(matching Lean's eliminator). The four cases correspond directly to
the four constructors of `BoundaryAdminEquiv`. -/
@[elab_as_elim] def generatedRec
    {motive :
      ∀ {Y₁ Y₂ : setup.BoundaryObject},
        @BoundaryAdminEquiv setup Y₁ Y₂ → Prop}
    (refl_case : ∀ Y, motive (BoundaryAdminEquiv.refl Y))
    (symm_case :
      ∀ {Y₁ Y₂ : setup.BoundaryObject}
        {h : @BoundaryAdminEquiv setup Y₁ Y₂},
        motive h → motive h.symm)
    (trans_case :
      ∀ {Y₁ Y₂ Y₃ : setup.BoundaryObject}
        {h₁ : @BoundaryAdminEquiv setup Y₁ Y₂}
        {h₂ : @BoundaryAdminEquiv setup Y₂ Y₃},
        motive h₁ → motive h₂ → motive (h₁.trans h₂))
    (gen_case :
      ∀ {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
        {h : IndependentSinks R s t}
        {Y₁ Y₂ : setup.BoundaryObject}
        (hSwap : BoundaryTwoStepSwap h Y₁ Y₂),
        motive (BoundaryAdminEquiv.ofTwoStepSwap hSwap))
    {Y₁ Y₂ : setup.BoundaryObject}
    (h : @BoundaryAdminEquiv setup Y₁ Y₂) : motive h := by
  induction h with
  | refl Y => exact refl_case Y
  | symm _ ih => exact symm_case ih
  | trans _ _ ih₁ ih₂ => exact trans_case ih₁ ih₂
  | ofTwoStepSwap hSwap => exact gen_case hSwap

end BoundaryAdminEquiv

/-! ## Item 5q — Manuscript-facing theorem aliases

Re-exports of the items above under names mirroring the manuscript's
canonicality clause for `thm:canonical-reconstruction-algorithm`
(L1180). These carry **no** new content. -/

namespace PeelChain

/-- **Manuscript alias (5q.a)**: *canonical frontier observations are
stable under contextual admin moves modulo
`BoundaryAdminEquiv`.* Pointer to
[`contextual_admin_move_word_stable`]. -/
theorem theorem_canonical_frontier_observation_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    FrontierWord.Equiv
      (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  contextual_admin_move_word_stable m

/-- **Manuscript alias (5q.b)**: *the canonical frontier word descends
through contextual admin equivalence.* Pointer to
[`contextual_admin_equiv_word_stable`]. -/
theorem theorem_canonical_frontier_word_descends_through_contextual_admin_equiv
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    FrontierWord.Equiv
      (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  contextual_admin_equiv_word_stable h

end PeelChain

/-- **Manuscript alias (5q.c)**: *canonicality is modulo
`BoundaryAdminEquiv`, not strict equality.*

This is a definitional pointer: `FrontierWord.Equiv` is by definition
`RecordStructEquiv BoundaryAdminEquiv` on residues — i.e. the
canonical frontier word is observed up to the generated-by-two-step-swaps
boundary closure, *not* up to literal equality of records. -/
theorem theorem_canonicality_modulo_boundary_admin_equiv
    (w₁ w₂ : FrontierWord setup) :
    FrontierWord.Equiv w₁ w₂ ↔
      RecordStructEquiv (@BoundaryAdminEquiv setup) w₁.residue w₂.residue :=
  Iff.rfl

/-
TEX ref: our_paper_draft.tex, label def:local-semantic-signature (L1360+)
Paper role: the local semantic signature of a frontier word classifies it
  by sort, generator family (Corr/Loc/Nis/A1/Env), and adjacency data
Lean status: MISSING → definition stub added (M3)
  Placed here (CanonicalFrontierWord.lean) because FrontierWord is defined here;
  original placement in RewriteCalculus.lean was incorrect (FrontierWord not in scope there).
-/
/-- **`def:local-semantic-signature`**: the local semantic signature of a
frontier rewrite rule, classifying it into one of the five geometric generator
families (Corr, Loc, Nis, A1, Env) plus the relevant adjacency data.

The signature is the classification data extracted from the rule's boundary
structure that determines which CanNF rule family the rule belongs to. -/
structure LocalSemanticSignature (setup : RewriteCalculusSetup.{u}) where
  /-- The underlying frontier word being classified. -/
  word : FrontierWord setup
  /-- Which of the five generator families this word falls under
  (Corr / Loc / Nis / A1 / Env). Carried as a Prop field until the
  concrete classification function is implemented. -/
  familyMembership : Prop
  /-- Adjacency data: which boundary interfaces are connected by this rule. -/
  adjacencyData : Prop

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
