import TraceCalc.LayerB.RealObjects.CanNFObligations

/-!
# Real-objects formalization: CanNF algorithm-design layer (items 6a–6e)

**Phase 3B items 6a–6e (2026-04-24).** This file introduces the
**algorithm-design interface layer** for a future canonical-normal-form
construction on `FrontierWord`. It is **not an implementation**: it
fixes the *shape* of the future normal form, the *local reduction
contract*, and the *correctness obligations* a future executable
normalizer must discharge.

## Items in this file

* **6a** — `FrontierNF setup`: skeletal normal-form carrier (a
  `FrontierWord` plus a Prop-valued normality certificate); equivalence
  inherited from `FrontierWord.Equiv`.
* **6b** — `FrontierReductionSystem setup`: local reduction contract
  with `Step`, `IsNormal`, `measure`, `step_sound`, `step_decreases`,
  `normal_no_step`, `stuck_is_normal`.
* **6c** — `FrontierReductionSystem.MultiStep`: reflexive-transitive
  closure of `Step`, with `MultiStep.sound`. `NormalResult` packaging.
* **6d** — `FrontierNormalizerAlgorithm`: the *choice of terminating
  normal result* obligation. `FrontierNormalizerCorrectness`: the
  global correctness obligations (sound/complete normalizer, boundary
  compat, normal uniqueness/confluence).
  `FrontierNormalizerCorrectness.toCanNFObligations`: bridge into the
  5v registry.
* **6e** — Manuscript-facing TODO aliases.

## Honest scope (per user's stop conditions, all honored)

* **No concrete normalizer is implemented.** `FrontierNormalizerAlgorithm`
  is a structure obligation, never instantiated.
* **No completeness theorem is proved here.** `complete_normalizer` is a
  field of `FrontierNormalizerCorrectness`, never closed.
* **No confluence is proved here.** `normal_unique` is an obligation
  field, never closed.
* **No fake equality of normal forms.** Local step soundness yields
  `FrontierWord.Equiv` between intermediate states (via `MultiStep.sound`),
  **not** equality of chosen normal outputs. The latter requires
  `normal_unique` (confluence/canonical-choice), which is exposed as a
  separate explicit obligation.

## The architectural distinction

  local step soundness  ⟹  multi-step equivalence       (proved here)
  local step soundness  ⟹  canonical equality of NFs    (NOT proved)

The second arrow requires `normal_unique` (confluence /
canonical-representative choice). That is the precise obligation a
future CanNF algorithm must discharge.

## Global invariants honored

* `INV CanNF-Contract`: completeness remains a contract obligation;
  `complete_normalizer` is a field of `FrontierNormalizerCorrectness`,
  not a manufactured theorem.
* `INV Build-Trust-Gate`: validated by full `lake build`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **algorithm-shape obligations** this layer isolates.
* L1186–L1192 — per-step descent that the local reduction contract
  generalizes.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain
open PeelChain
open PeelChain.FrontierObservation

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 6a — Normal-form shape draft (`FrontierNF`) -/

/-- **`FrontierNF setup`**: skeletal normal-form carrier.

`FrontierNF` is *only* a normal-form carrier. The proof that the word
is actually normal is `Prop`-valued; the semantic data remains in
`word`. **This is not a quotient and not an implementation of CanNF.**

The `is_normal` field is intentionally a bare `Prop` (rather than a
predicate parameterized by some specific reduction system) so that
`FrontierNF` is implementation-neutral: different reduction systems
can populate `is_normal` with their own `IsNormal` predicate. -/
structure FrontierNF (setup : RewriteCalculusSetup.{u}) where
  /-- The underlying canonical-frontier-word representative. -/
  word : FrontierWord setup
  /-- A `Prop`-valued normality certificate. Implementation-neutral:
  populated by `S.IsNormal r.nf_word` when constructed from a
  `NormalResult` of a reduction system `S`. -/
  is_normal : Prop

namespace FrontierNF

/-- The underlying frontier word of a normal form. -/
def underlying (n : FrontierNF setup) : FrontierWord setup := n.word

/-- **Equivalence on normal forms** induced from `FrontierWord.Equiv`. -/
def Equiv (n₁ n₂ : FrontierNF setup) : Prop :=
  FrontierWord.Equiv n₁.word n₂.word

namespace Equiv

/-- Reflexivity. -/
@[refl] theorem refl (n : FrontierNF setup) : Equiv n n :=
  FrontierWord.Equiv.refl _

/-- Symmetry. -/
@[symm] theorem symm {n₁ n₂ : FrontierNF setup}
    (h : Equiv n₁ n₂) : Equiv n₂ n₁ :=
  FrontierWord.Equiv.symm h

/-- Transitivity. -/
theorem trans {n₁ n₂ n₃ : FrontierNF setup}
    (h₁ : Equiv n₁ n₂) (h₂ : Equiv n₂ n₃) : Equiv n₁ n₃ :=
  FrontierWord.Equiv.trans h₁ h₂

end Equiv

end FrontierNF

/-! ## Item 6b — Local reduction contract (`FrontierReductionSystem`) -/

/-- **`FrontierReductionSystem setup`**: local rewriting data on
`FrontierWord`.

This is **not the normalizer**. It is the local reduction contract.
Termination follows from `step_decreases` over `Nat`, but the
*existence of a chosen normal form* for every word still requires an
algorithm/selection principle (supplied by
`FrontierNormalizerAlgorithm`).

Per `INV CanNF-Contract`: the local reduction contract is honest
about what it proves (each step is admin-equivalent to the previous
word) and about what it does not prove (canonicality / confluence /
existence of a single chosen normal form). -/
structure FrontierReductionSystem (setup : RewriteCalculusSetup.{u}) where
  /-- One-step reduction relation. -/
  Step : FrontierWord setup → FrontierWord setup → Prop
  /-- Predicate identifying normal (irreducible) words. -/
  IsNormal : FrontierWord setup → Prop
  /-- Termination measure. -/
  measure : FrontierWord setup → Nat
  /-- Soundness: each step preserves `FrontierWord.Equiv`. -/
  step_sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      Step w₁ w₂ → FrontierWord.Equiv w₁ w₂
  /-- Strict decrease of the measure under each step. -/
  step_decreases :
    ∀ {w₁ w₂ : FrontierWord setup},
      Step w₁ w₂ → measure w₂ < measure w₁
  /-- Normal forms admit no further step. -/
  normal_no_step :
    ∀ {w : FrontierWord setup},
      IsNormal w → ¬ ∃ w', Step w w'
  /-- Conversely, words admitting no step are normal. -/
  stuck_is_normal :
    ∀ {w : FrontierWord setup},
      (¬ ∃ w', Step w w') → IsNormal w

namespace FrontierReductionSystem

variable (S : FrontierReductionSystem setup)

/-- **A well-founded relation derived from the measure**: `S.Step`
itself is well-founded *up to the measure pullback* — i.e., the
relation `fun w₁ w₂ => S.measure w₁ < S.measure w₂` (which `S.Step`
satisfies in reverse via `step_decreases`) is well-founded by inverse
image of `Nat.lt`. The downstream `termination_witness` field of
`CanNFObligations` only demands existence of *some* well-founded
relation, satisfied by this measure-pullback. -/
theorem measureLt_wellFounded :
    WellFounded (fun w₁ w₂ : FrontierWord setup =>
      S.measure w₁ < S.measure w₂) :=
  InvImage.wf S.measure Nat.lt_wfRel.wf

/-! ## Item 6c — Multi-step reduction -/

/-- **Reflexive-transitive closure of `Step`**, as a local inductive. -/
inductive MultiStep : FrontierWord setup → FrontierWord setup → Prop
  | refl (w : FrontierWord setup) : MultiStep w w
  | trans {w₁ w₂ w₃ : FrontierWord setup}
      (h₁ : S.Step w₁ w₂) (h₂ : MultiStep w₂ w₃) : MultiStep w₁ w₃

namespace MultiStep

/-- Soundness of multi-step reduction: any sequence of reductions
preserves `FrontierWord.Equiv`. -/
theorem sound {w₁ w₂ : FrontierWord setup}
    (h : S.MultiStep w₁ w₂) : FrontierWord.Equiv w₁ w₂ := by
  induction h with
  | refl w => exact FrontierWord.Equiv.refl w
  | trans hStep _ ih =>
      exact FrontierWord.Equiv.trans (S.step_sound hStep) ih

/-- Convenience: a single step is a multi-step. -/
theorem step {w₁ w₂ : FrontierWord setup}
    (h : S.Step w₁ w₂) : S.MultiStep w₁ w₂ :=
  MultiStep.trans h (MultiStep.refl _)

/-- Convenience: explicit reflexive form. -/
theorem refl' (w : FrontierWord setup) : S.MultiStep w w :=
  MultiStep.refl w

end MultiStep

/-! ## Item 6c (continued) — Normal results -/

/-- **`NormalResult S w`**: a witness that `w` reduces to some normal
form.

Note: `NormalResult` records the *existence and identity* of a
particular normal form reached by some reduction sequence. **It does
not assert uniqueness** of that normal form across different
reduction sequences — that is the canonicality content, exposed
separately as `FrontierNormalizerCorrectness.normal_unique`. -/
structure NormalResult (w : FrontierWord setup) where
  /-- The chosen normal-form word. -/
  nf_word : FrontierWord setup
  /-- A reduction sequence from `w` to `nf_word`. -/
  reduces : S.MultiStep w nf_word
  /-- The chosen `nf_word` is normal. -/
  normal : S.IsNormal nf_word

namespace NormalResult

variable {S}

/-- Convert a `NormalResult` to a `FrontierNF`. The `is_normal` field
is populated with `S.IsNormal r.nf_word`. -/
def toFrontierNF {w : FrontierWord setup} (r : S.NormalResult w) :
    FrontierNF setup :=
  { word := r.nf_word, is_normal := S.IsNormal r.nf_word }

/-- A normal result is admin-equivalent to its source. Pure
consequence of `MultiStep.sound`; **does not** assert canonicality
of the chosen `nf_word`. -/
theorem sound {w : FrontierWord setup} (r : S.NormalResult w) :
    FrontierWord.Equiv w r.nf_word :=
  MultiStep.sound S r.reduces

@[simp] theorem toFrontierNF_word
    {w : FrontierWord setup} (r : S.NormalResult w) :
    r.toFrontierNF.word = r.nf_word := rfl

end NormalResult

end FrontierReductionSystem

/-! ## Item 6d — Algorithm + correctness obligations -/

/-- **`FrontierNormalizerAlgorithm setup S`**: the future
executable/constructive normalizer obligation against a given local
reduction contract `S`.

Providing this structure is **strictly stronger** than providing local
reduction rules: it chooses, for *every* word, a particular terminating
normal result. The algorithm content is the function `normalize`; the
local reduction system `S` only constrains what the steps look like
and that the measure decreases.

Per `INV CanNF-Contract`: this is **not instantiated** here. -/
structure FrontierNormalizerAlgorithm
    (setup : RewriteCalculusSetup.{u})
    (S : FrontierReductionSystem setup) where
  /-- Choice of a terminating normal result for every word. -/
  normalize : (w : FrontierWord setup) → S.NormalResult w

/-- **`FrontierNormalizerCorrectness S A`**: the global correctness
obligations a future canonical-normal-form algorithm `A` (against the
local reduction system `S`) must discharge.

These are the *substantive* obligations — none is provable from local
reduction soundness alone. In particular:

* `sound_normalizer` demands that admin-equivalent words produce the
  *exact same* `FrontierNF` output, not merely admin-equivalent
  outputs. That requires the algorithm to make a canonical choice of
  normal form within each equivalence class.
* `complete_normalizer` demands that equality of chosen outputs
  implies admin-equivalence — the converse canonicality content.
* `normal_unique` demands confluence / canonical-representative
  uniqueness within the local reduction system.

Per `INV CanNF-Contract`: instantiating any of these fields is a
substantive mathematical commitment. -/
structure FrontierNormalizerCorrectness
    {setup : RewriteCalculusSetup.{u}}
    (S : FrontierReductionSystem setup)
    (A : FrontierNormalizerAlgorithm setup S) where
  /-- **Canonical soundness**: admin-equivalent inputs produce
  identical normal-form outputs.

  This is **stronger** than local step soundness. Local step soundness
  (via `MultiStep.sound`) only gives that each input is
  admin-equivalent to its own normal form — it does not relate the
  normal forms of two distinct admin-equivalent inputs. Genuine
  canonicality is required here. -/
  sound_normalizer :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        (A.normalize w₁).toFrontierNF = (A.normalize w₂).toFrontierNF
  /-- **Canonical completeness**: equal chosen outputs imply admin
  equivalence. Per `INV CanNF-Contract`: this is the actual
  canonicality detection obligation. -/
  complete_normalizer :
    ∀ {w₁ w₂ : FrontierWord setup},
      (A.normalize w₁).toFrontierNF = (A.normalize w₂).toFrontierNF →
        FrontierWord.Equiv w₁ w₂
  /-- **Boundary-admin compatibility on the underlying word.** A
  weaker companion to `sound_normalizer`: even where strict equality
  of outputs is too strong, the underlying frontier words remain
  admin-equivalent. -/
  boundary_admin_compat :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        FrontierWord.Equiv
          (A.normalize w₁).toFrontierNF.word
          (A.normalize w₂).toFrontierNF.word
  /-- **Normal-form uniqueness / confluence**: any two normal forms
  reachable from the same word along any pair of reduction sequences
  are admin-equivalent. This is the genuine confluence obligation —
  **not** derivable from `step_sound` + `step_decreases` alone. -/
  normal_unique :
    ∀ {w n₁ n₂ : FrontierWord setup},
      S.MultiStep w n₁ →
      S.MultiStep w n₂ →
      S.IsNormal n₁ →
      S.IsNormal n₂ →
      FrontierWord.Equiv n₁ n₂

namespace FrontierNormalizerCorrectness

variable {S : FrontierReductionSystem setup}
variable {A : FrontierNormalizerAlgorithm setup S}
variable (C : FrontierNormalizerCorrectness S A)

/-- **Bridge to the 5v registry.**

A complete normalizer-correctness witness instantiates the
`CanNFObligations` registry with target type `FrontierNF setup` and
normalize function `fun w => (A.normalize w).toFrontierNF`. Each field
of the registry is filled by an explicit field of `C` — *no obligation
is manufactured here from local step data alone.* -/
def toCanNFObligations :
    CanNFObligations setup (FrontierNF setup)
      (fun w => (A.normalize w).toFrontierNF) where
  termination_witness :=
    ⟨InvImage Nat.lt S.measure, InvImage.wf S.measure Nat.lt_wfRel.wf⟩
  sound := C.sound_normalizer
  complete := C.complete_normalizer
  boundary_admin_compat := fun h => C.sound_normalizer h
  contextual_admin_stable := fun h =>
    C.sound_normalizer (PeelChain.contextual_admin_equiv_word_stable h)

end FrontierNormalizerCorrectness

/-! ## Item 6e — Manuscript-facing TODO aliases -/

/-- **Manuscript alias (6e.1)**: local reduction step soundness is an
*obligation field* of any `FrontierReductionSystem`. Pointer to
[`FrontierReductionSystem.step_sound`]. -/
theorem theorem_cannf_reduction_step_soundness_obligation
    (S : FrontierReductionSystem setup)
    {w₁ w₂ : FrontierWord setup} (h : S.Step w₁ w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  S.step_sound h

/-- **Manuscript alias (6e.2)**: local reduction step strictly
decreases the measure. Pointer to
[`FrontierReductionSystem.step_decreases`]. -/
theorem theorem_cannf_reduction_step_decreases_obligation
    (S : FrontierReductionSystem setup)
    {w₁ w₂ : FrontierWord setup} (h : S.Step w₁ w₂) :
    S.measure w₂ < S.measure w₁ :=
  S.step_decreases h

/-- **Manuscript alias (6e.3)**: a normal result is admin-equivalent
to its source word. Pointer to
[`FrontierReductionSystem.NormalResult.sound`]. -/
theorem theorem_cannf_normal_result_sound
    {S : FrontierReductionSystem setup} {w : FrontierWord setup}
    (r : S.NormalResult w) :
    FrontierWord.Equiv w r.nf_word :=
  r.sound

/-- **Manuscript alias (6e.4)**: normal-form uniqueness / confluence
is an *obligation field* of `FrontierNormalizerCorrectness`. Pointer
to [`FrontierNormalizerCorrectness.normal_unique`]. -/
theorem theorem_cannf_normal_uniqueness_obligation
    {S : FrontierReductionSystem setup}
    {A : FrontierNormalizerAlgorithm setup S}
    (C : FrontierNormalizerCorrectness S A)
    {w n₁ n₂ : FrontierWord setup}
    (h₁ : S.MultiStep w n₁) (h₂ : S.MultiStep w n₂)
    (hN₁ : S.IsNormal n₁) (hN₂ : S.IsNormal n₂) :
    FrontierWord.Equiv n₁ n₂ :=
  C.normal_unique h₁ h₂ hN₁ hN₂

/-- **Manuscript alias (6e.5)**: from algorithm correctness, derive
the full `CanNFObligations` registry. Pointer to
[`FrontierNormalizerCorrectness.toCanNFObligations`]. -/
def theorem_cannf_algorithm_correctness_to_obligations
    {S : FrontierReductionSystem setup}
    {A : FrontierNormalizerAlgorithm setup S}
    (C : FrontierNormalizerCorrectness S A) :
    CanNFObligations setup (FrontierNF setup)
      (fun w => (A.normalize w).toFrontierNF) :=
  C.toCanNFObligations

/-- **Manuscript alias (6e.6)**: completeness is an *obligation field*
of `FrontierNormalizerCorrectness`, NEVER derivable from local
reduction data alone. Pointer to
[`FrontierNormalizerCorrectness.complete_normalizer`]. -/
theorem theorem_cannf_completeness_obligation
    {S : FrontierReductionSystem setup}
    {A : FrontierNormalizerAlgorithm setup S}
    (C : FrontierNormalizerCorrectness S A)
    {w₁ w₂ : FrontierWord setup}
    (h : (A.normalize w₁).toFrontierNF = (A.normalize w₂).toFrontierNF) :
    FrontierWord.Equiv w₁ w₂ :=
  C.complete_normalizer h

/-
TEX ref: our_paper_draft.tex, label prop:local-confluence (L1380+)
Paper role: the CanNF rewrite system satisfies local confluence (diamond property);
  join rules (join-corr-corr, join-corr-loc, etc.) provide the joinability witnesses
Lean status: MISSING → stub added (M3); local_diamond obligation already in FrontierConfluenceObligations
-/
/-
TEX ref: our_paper_draft.tex, label lem:local-generation-trace-equivalence (L1415+)
Paper role: local generation of the rewrite system implies trace equivalence;
  two traces locally reachable by the generator family are equivalent
Lean status: MISSING → stub added (M3); follows from contextual_admin_equiv_word_stable
  Moved here from CanonicalFrontierWord.lean because FrontierReductionSystem is defined here.
-/
/-- **`lem:local-generation-trace-equivalence`**: local generation by the
CanNF rule families implies trace equivalence.

If two frontier words are related by a single step of the CanNF rewrite system
(i.e., one step of the `FrontierRuleSystem`), they are `FrontierWord.Equiv`.
This follows from the soundness of each rewrite step: every rule step preserves
the equivalence class.

The named statement here captures the manuscript's congruence generation
lemma: reachability in the rewrite system is contained in `FrontierWord.Equiv`. -/
structure LocalGenerationTraceEquivalence
    (setup : RewriteCalculusSetup.{u}) : Prop where
  /-- A single rewrite step implies frontier-word equivalence. -/
  step_implies_equiv :
    ∀ (S : FrontierReductionSystem setup) (w₁ w₂ : FrontierWord setup),
      S.Step w₁ w₂ → FrontierWord.Equiv w₁ w₂
  /-- Reachability (multi-step) implies frontier-word equivalence. -/
  reachable_implies_equiv :
    ∀ (S : FrontierReductionSystem setup) (w₁ w₂ : FrontierWord setup),
      S.MultiStep w₁ w₂ → FrontierWord.Equiv w₁ w₂

/-- **`localGenerationTraceEquivalence`** (PROVED):
Both fields follow directly from the `FrontierReductionSystem` contract:
`step_implies_equiv` is exactly `S.step_sound`, and `reachable_implies_equiv`
is exactly `FrontierReductionSystem.MultiStep.sound` (proved by induction on the
multi-step sequence using `step_sound`). -/
theorem localGenerationTraceEquivalence
    (setup : RewriteCalculusSetup.{u}) :
    LocalGenerationTraceEquivalence setup where
  step_implies_equiv := fun S _w₁ _w₂ h => S.step_sound h
  reachable_implies_equiv := fun _S _w₁ _w₂ h => h.sound

/-- **`prop:local-confluence`**: the CanNF frontier rewrite system satisfies local
confluence (the diamond / Church-Rosser property).

In the manuscript, local confluence is established by exhibiting joinability
witnesses for each pair of critical pairs in the join-rule families
(join-corr-corr, join-corr-loc, join-corr-desc, join-desc-a1, join-env).
The `FrontierConfluenceObligations.local_diamond` field already registers
this as an obligation; `local_confluence` names the full confluence statement
that follows from it (by Newman's lemma, since the system is also terminating). -/
def local_confluence
    (setup : RewriteCalculusSetup.{u})
    (S : FrontierReductionSystem setup) : Prop :=
  ∀ (w w₁ w₂ : FrontierWord setup),
    S.MultiStep w w₁ → S.MultiStep w w₂ →
      ∃ w' : FrontierWord setup, S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
