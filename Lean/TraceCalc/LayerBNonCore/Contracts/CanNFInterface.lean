import TraceCalc.LayerB.RealObjects.CanonicalFrontierWord

/-!
# Real-objects formalization: canonical normal form interface (items 5r–5u)

**Phase 3B items 5r–5u (2026-04-24).** This file introduces the
**canonical normal form (CanNF) interface contract** for
`FrontierWord` and proves the descent theorem available against any
sound normalizer. **No bogus normalizer is instantiated** (per the
user's stop condition); soundness and completeness are exposed as
typeclass contracts, not as theorems with manufactured proofs.

## Items in this file

* **5r** — `FrontierWordSoundNormalizer setup` and
  `FrontierWordCompleteNormalizer setup` structures (split, since
  completeness would amount to canonical normalization itself);
  optional combined `FrontierWordNormalizer` wrapper.
* **5s** — `contextual_admin_equiv_normalize_eq` consuming a
  `FrontierWordSoundNormalizer` and the descent theorem
  `contextual_admin_equiv_word_stable` (item 5o).
* **5t** — `normalize_eq_iff_frontier_word_equiv` *stated as the
  contract* (one direction is `sound`, the other is `complete`); two
  manuscript-facing aliases.
* **5u** — Map / memory / sync handled outside this file.

## Honest scope (per user's stop conditions)

* The contract is **not** instantiated with a normalizer. The
  manuscript phrase *"canonical normal form detects administrative
  equivalence"* is recorded here as a **theorem against the
  contract**, not as a closed theorem of Lean. Any future CanNF
  construction (full canonical normalization machinery) must supply a
  `FrontierWordSoundNormalizer` (cheap if administrative tracking is
  added to the normalizer's intermediate state) and a
  `FrontierWordCompleteNormalizer` (the *actual* canonicality
  obligation).
* `FrontierWord.Equiv` is **not** made proof-irrelevant. The contract
  takes `FrontierWord.Equiv w₁ w₂` as a hypothesis, not as data; the
  semantic content carried by the equivalence proof (which two-step
  swap produced this descent) is preserved.

## Global invariants honored

* `INV AdminMove-Nonvacuity`: the descent theorem at 5s consumes the
  5o descent theorem (which routes through
  `peelSink_swap_structEquiv_admin`); the normalizer contract adds
  one further hop (sound) and obtains the equation.
* `INV CanNF-Contract` (newly recorded): completeness of the canonical
  normal form is treated as a contract obligation, NOT as a theorem
  manufactured from frontier-equivalence machinery. Quietly closing
  `complete` would assume the manuscript's main canonicality theorem.
* `INV Build-Trust-Gate`: validated by full `lake build` before status
  sync.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **CanNF detection** content this file expresses as a
  contract. The 5o descent is the soundness side; the as-yet-unbuilt
  CanNF is the completeness side.
* L1186–L1192 — the per-step descent whose normalizer image is the
  invariant.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 5r — CanNF interface contract -/

/-- **Sound normalizer for `FrontierWord setup`.**

A `FrontierWordSoundNormalizer setup` packages a target type `NF`
together with a normalization function `normalize : FrontierWord setup → NF`
that **collapses `FrontierWord.Equiv` to equality** in `NF`.

This is the *cheap half* of the manuscript's CanNF promise: any
administrative tracker that records all `BoundaryAdminEquiv`-relevant
content from the residue (e.g., a multiset/perm-quotient of boundary
data combined with the strict interior fields) discharges this
contract. Completeness — that *only* admin-equivalent words have equal
normal forms — is the *actual canonicality obligation* and is exposed
separately in `FrontierWordCompleteNormalizer`. -/
structure FrontierWordSoundNormalizer (setup : RewriteCalculusSetup.{u}) where
  /-- The normal-form target. -/
  NF : Type v
  /-- The normalization function. -/
  normalize : FrontierWord setup → NF
  /-- Soundness: admin-equivalent words have equal normal forms. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂

/-- **Complete normalizer for `FrontierWord setup`.**

The converse of `FrontierWordSoundNormalizer.sound`: words with equal
normal forms are admin-equivalent. **This is the actual canonicality
obligation** — proving `complete` for any concrete normalizer
discharges the manuscript's *"canonical normal form detects
administrative equivalence"* claim.

Per `INV CanNF-Contract`: this is **not** instantiated here; it is
recorded as the contract whose discharge is the substantive future
work. -/
structure FrontierWordCompleteNormalizer (setup : RewriteCalculusSetup.{u})
    extends FrontierWordSoundNormalizer setup where
  /-- Completeness: words with equal normal forms are admin-equivalent. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂

/-- **Combined contract**: a normalizer that is both sound and
complete. This is exactly the manuscript's CanNF interface.

Definitionally `FrontierWordCompleteNormalizer setup`; this alias
exists for naming parity with the manuscript's "canonical normal
form" terminology. -/
abbrev FrontierWordNormalizer (setup : RewriteCalculusSetup.{u}) :=
  FrontierWordCompleteNormalizer setup

namespace FrontierWordSoundNormalizer

/-- Convenience accessor: dot-notation `N.normalize w` is already
available; this `simp`-friendly alias spells out that `sound` is
literally an equation between normal-form values. -/
theorem normalize_eq_of_equiv (N : FrontierWordSoundNormalizer setup)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    N.normalize w₁ = N.normalize w₂ :=
  N.sound h

end FrontierWordSoundNormalizer

/-! ## Item 5s — Descent through normalizer soundness -/

namespace PeelChain

/-- **Item 5s: `contextual_admin_equiv_normalize_eq`.**

Against any sound normalizer `N`, the canonical normal forms of two
chains' frontier words at common depth `d` are equal whenever the
chains are contextually admin equivalent at depth `d`.

**Routing**: `contextual_admin_equiv_word_stable` (item 5o) →
`FrontierObservation.ofContextualAdminEquiv` (item 5l) →
`ContextualAdminEquiv.residueAt_structEquiv_admin` (item 5i) →
`ContextualAdminMove.residueAt_structEquiv_admin` (item 5h) →
`AdminMove.residueAt_2_structEquiv_admin` (item 5g) →
`peelSink_swap_structEquiv_admin` (item 5e-ii). The normalizer
soundness adds one more hop and converts the descent into an equation
in `N.NF`.

**Per `INV AdminMove-Nonvacuity`**: every step routes through the
local two-step swap content, never through full replay. -/
theorem contextual_admin_equiv_normalize_eq
    (N : FrontierWordSoundNormalizer setup)
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  N.sound (contextual_admin_equiv_word_stable h)

/-- **Move-level corollary**: the descent equation at the move level. -/
theorem contextual_admin_move_normalize_eq
    (N : FrontierWordSoundNormalizer setup)
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  N.sound (contextual_admin_move_word_stable m)

end PeelChain

/-! ## Item 5t — Equality detection theorem (against the contract) -/

/-- **Item 5t: `normalize_eq_iff_frontier_word_equiv`.**

Against a *complete* normalizer (i.e. one supplying both `sound` and
`complete`), normal-form equality coincides with `FrontierWord.Equiv`.

Per `INV CanNF-Contract`: the forward direction is `complete`, the
backward direction is `sound`. **Both directions are contract
obligations**; this theorem is the precise statement of the
manuscript's *"canonical normal form detects administrative
equivalence"* claim, parameterized over any future CanNF instance.

This file does **not** discharge either direction by manufacturing a
normalizer; it states the equivalence so consumers can quote it once
a real normalizer is supplied. -/
theorem normalize_eq_iff_frontier_word_equiv
    (N : FrontierWordCompleteNormalizer setup)
    (w₁ w₂ : FrontierWord setup) :
    N.normalize w₁ = N.normalize w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨N.complete, N.sound⟩

namespace PeelChain

/-- **Manuscript alias (5t.a)**: *the canonical normal form is sound
under contextual administrative equivalence.* Pointer to
[`PeelChain.contextual_admin_equiv_normalize_eq`]. -/
theorem theorem_frontier_cannf_sound_under_admin_equiv
    (N : FrontierWordSoundNormalizer setup)
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = N.normalize
        (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  contextual_admin_equiv_normalize_eq N h

end PeelChain

/-- **Manuscript alias (5t.b)**: *the canonical normal form detects
contextual administrative equivalence.* Pointer to
[`normalize_eq_iff_frontier_word_equiv`].

This is the manuscript's CanNF detection statement against a
hypothetical complete normalizer; it is the **canonicality theorem
modulo the CanNF contract**. -/
theorem theorem_frontier_cannf_detects_admin_equiv
    (N : FrontierWordCompleteNormalizer setup)
    (w₁ w₂ : FrontierWord setup) :
    N.normalize w₁ = N.normalize w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  normalize_eq_iff_frontier_word_equiv N w₁ w₂

/-
TEX ref: our_paper_draft.tex, label lem:normalization-congruence-generation (L1400+)
Paper role: normalization is a congruence with respect to frontier-word equivalence;
  the normalizer collapses the equivalence relation to equality
Lean status: MISSING → stub added (M3); follows from FrontierWordSoundNormalizer.sound
-/
/-- **`lem:normalization-congruence-generation`**: normalization generates
the frontier-word congruence.

A sound normalizer collapses `FrontierWord.Equiv` to equality: if `w₁ ~ w₂`
then `N.normalize w₁ = N.normalize w₂`. This is precisely
`FrontierWordSoundNormalizer.sound`, which already exists in this file.

The named alias `normalization_congruence_generation` makes the manuscript
lemma reference explicit. -/
theorem normalization_congruence_generation
    (N : FrontierWordSoundNormalizer setup)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    N.normalize w₁ = N.normalize w₂ :=
  N.sound h

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
