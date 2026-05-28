import TraceCalc.LayerBNonCore.Contracts.CanNFInterface

/-!
# Real-objects formalization: CanNF obligation registry (items 5v–5z)

**Phase 3B items 5v–5z (2026-04-24).** This file introduces a
**theorem-obligation registry** for any future canonical-normal-form
implementation on `FrontierWord`. It is **deliberately non-executable
content**: the registry names the proof obligations a future CanNF
construction must discharge to instantiate
`FrontierWordCompleteNormalizer`. No obligation is proved here unless
it is *immediate from existing contracts* (5y).

## Items in this file

* **5v** — `CanNFObligations setup N` structure: a registry of named
  proof targets (termination, soundness, completeness, boundary-admin
  compatibility, contextual-admin stability) parameterized over a
  prospective `NF`-target type and `normalize` function.
* **5w** — Manuscript-facing TODO theorem aliases: each obligation is
  re-exported under a manuscript-style name. **Not proved**; stated as
  obligation pointers.
* **5x** — Dependency DAG: docstrings on each obligation enumerate the
  earlier formal theorems the obligation **may consume** vs. those
  that explicitly do **not** suffice. Records that completeness is
  NOT derivable from 5e–5s alone.
* **5y** — Non-circularity audit theorems: type-level separation
  statements showing that descent (5s) needs only the `Sound` half
  while equality detection (5t) needs the `Complete` half. Stated
  as `Iff.rfl`/`Eq.rfl`-level definitional pointers — no faked content.
* **5z** — Map / status / memory sync (handled outside this file).

## Honest scope (per user's stop conditions, all honored)

* No obligation in this file is proved by assuming the theorem it is
  meant to prove. The `complete` obligation is recorded as an
  obligation only — never as a closed theorem.
* No completeness proof appears without a concrete normalizer (none
  is supplied here).
* The registry is **interface-shaped**, not implementation-shaped:
  fields name what must be proved, not how it must be proved.

## Global invariants honored

* `INV CanNF-Contract`: completeness is recorded as a contract
  obligation, NOT manufactured from 5e–5s.
* `INV AdminMove-Nonvacuity`: every claim that *is* proved (the 5y
  audit theorems) routes through the contract structure of items
  5r–5s/5t, which themselves route through
  `peelSink_swap_structEquiv_admin`.
* `INV Build-Trust-Gate`: validated by full `lake build`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **outstanding CanNF construction obligation** this
  registry isolates.
* L1186–L1192 — per-step descent.
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

/-! ## Item 5v — CanNF obligation registry -/

/-- **`CanNFObligations setup NF normalize`**: the registry of proof
obligations a future canonical-normal-form construction must
discharge in order to instantiate `FrontierWordCompleteNormalizer`
with target type `NF` and normalization function `normalize`.

Per `INV CanNF-Contract`: this structure **names** the obligations;
it does NOT prove them. Instantiating any field is a substantive
mathematical commitment.

Each field's docstring (item 5x) enumerates the earlier formal
theorems the obligation **may consume** and explicitly records when
an obligation is **not** derivable from existing material. -/
structure CanNFObligations
    (setup : RewriteCalculusSetup.{u})
    (NF : Type v)
    (normalize : FrontierWord setup → NF) where
  /-- **Termination / well-foundedness obligation.**

  If the normalization procedure is algorithmic — i.e. defined by a
  recursion on a structural measure of `FrontierWord` (or of the
  underlying residue record) — there must be a well-founded relation
  on `FrontierWord setup` strictly decreased at each rewrite step.
  Stated here as the existence of any such relation; the discharge
  obligation supplies a concrete one.

  **May consume**: nothing in items 5e–5t (those theorems are about
  the equivalence relation, not the rewrite system).
  **Cannot consume**: any of 5e–5t — termination is a property of the
  *normalizer*, not of the equivalence. -/
  termination_witness :
    Σ' (rel : FrontierWord setup → FrontierWord setup → Prop),
      WellFounded rel

  /-- **Soundness obligation**: `normalize` collapses
  `FrontierWord.Equiv` to equality.

  **May consume**: items 5o (`contextual_admin_equiv_word_stable`),
  5n (the `FrontierWord.Equiv` definition itself), 5e–5l (the entire
  ladder feeding 5o). A sound normalizer that records every
  `BoundaryAdminEquiv`-relevant content from the residue (e.g., a
  multiset/perm-quotient on boundary data combined with the strict
  interior fields) discharges this — *cheap half* of the contract. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → normalize w₁ = normalize w₂

  /-- **Completeness obligation**: equal normal forms imply
  `FrontierWord.Equiv`.

  **Cannot consume**: any of items 5e–5t. Completeness requires
  showing that the normalizer's choice of canonical representative
  faithfully *separates* admin-equivalence classes — a property of
  the rewriting system / classification machinery itself, not of the
  descent ladder. *This is the actual canonicality obligation.*

  Per `INV CanNF-Contract`: this field is the manuscript's
  outstanding canonicality construction obligation. Quietly closing
  it would assume the manuscript's main theorem. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      normalize w₁ = normalize w₂ → FrontierWord.Equiv w₁ w₂

  /-- **Boundary-admin compatibility obligation**: the normalizer
  respects the generated boundary-admin closure on residue boundary
  objects.

  Concretely: any `BoundaryAdminEquiv`-related pair of boundary
  objects, when wrapped into otherwise-identical residue records and
  then into `FrontierWord`s, must produce equal normal forms. This
  is a *strict subcase of `sound`* (since `BoundaryAdminEquiv` on
  boundary objects lifts to `RecordStructEquiv BoundaryAdminEquiv`
  on records via `RecordStructEquiv.refl`-on-everything-else +
  `Y_rel := the boundary equivalence`); we record it as an explicit
  obligation because manuscript-level canonicality discussions cite
  it directly.

  **May consume**: 5p (`BoundaryAdminEquiv.generatedRec`), 5o
  (subsumes via `sound`).
  **Cannot consume**: any field that would implicitly use
  `complete`. -/
  boundary_admin_compat :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        normalize ⟨R₁⟩ = normalize ⟨R₂⟩

  /-- **Contextual-admin stability obligation**: the normalizer is
  invariant under contextual administrative equivalence at the chain
  level.

  Concretely: contextually-admin-equivalent observations of two
  chains have equal normal forms after passing through
  `canonicalFrontierWord`.

  **May consume**: 5o (`contextual_admin_equiv_word_stable`), 5s
  (`contextual_admin_equiv_normalize_eq` against the same `sound`
  field), 5l (`FrontierObservation.ofContextualAdminEquiv`).
  **Subsumed by**: `sound` (this obligation is exactly the
  observation-level instance of `sound` for chain pairs related by
  `ContextualAdminEquiv`); recorded as a separate field for
  manuscript citability. -/
  contextual_admin_stable :
    ∀ {R : CompletedReconstructionRecord setup} {d : Nat}
      {c₁ c₂ : PeelChain R}
      (_h : ContextualAdminEquiv d c₁ c₂),
      normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
        = normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d))

namespace CanNFObligations

/-! ## Item 5w — Manuscript-facing TODO theorem aliases

These re-export the `CanNFObligations` fields under manuscript-style
names so that downstream code citing the manuscript can name a
specific obligation rather than a structure-field projection.
**Each is just `O.fieldname`** — no manufactured content.

Per the user's verbatim 5w stop condition: *"Do not prove them unless
they are immediate from existing contracts."* Each obligation IS
literally a structure field of the registry; the alias is the
appropriate "immediate" form. -/

variable {NF : Type v} {normalize : FrontierWord setup → NF}
variable (O : CanNFObligations setup NF normalize)
include O

/-- **Manuscript obligation alias (5w.1)**: well-founded normalization
measure exists. -/
def obligation_termination_witness :
    Σ' (rel : FrontierWord setup → FrontierWord setup → Prop),
      WellFounded rel :=
  O.termination_witness

/-- **Manuscript obligation alias (5w.2)**: soundness w.r.t.
`FrontierWord.Equiv`. -/
theorem obligation_sound
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    normalize w₁ = normalize w₂ :=
  O.sound h

/-- **Manuscript obligation alias (5w.3)**: completeness w.r.t.
`FrontierWord.Equiv`. **NOT** derivable from items 5e–5s; this is the
substantive canonicality construction obligation. -/
theorem obligation_complete
    {w₁ w₂ : FrontierWord setup}
    (h : normalize w₁ = normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  O.complete h

/-- **Manuscript obligation alias (5w.4)**: boundary-admin
compatibility. -/
theorem obligation_boundary_admin_compat
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    normalize ⟨R₁⟩ = normalize ⟨R₂⟩ :=
  O.boundary_admin_compat h

/-- **Manuscript obligation alias (5w.5)**: contextual-admin
stability. -/
theorem obligation_contextual_admin_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  O.contextual_admin_stable h

/-! ## Item 5x — Dependency DAG / consumption chart

The per-field docstrings above (5v) already enumerate the obligation
DAG. The following table gives the manuscript-facing summary:

```
  Obligation                  | May consume        | Cannot consume
  ----------------------------|--------------------|-----------------
  termination_witness         | (independent)      | 5e–5t
  sound                       | 5e–5o, 5n          | 5y completeness
  complete                    | (none of 5e–5t)    | 5e–5t
  boundary_admin_compat       | 5p, sound          | complete
  contextual_admin_stable     | 5o, 5s, 5l        | complete
```

**Headline non-derivability claim** (recorded as a docstring fact,
not a Lean theorem because it would require defining a meta-level
"derivable from" relation): `complete` is **not** derivable from any
combination of 5e through 5s. The 5e–5l ladder produces an
equivalence relation (`FrontierWord.Equiv`); 5o lifts admin moves
into it; 5r–5s sends the equivalence forward through `normalize`. No
amount of forward direction recovers a *separating* property of
`normalize` — that requires the rewriting system itself.
-/

/-! ## Item 5y — Non-circularity audit -/

/-- **Item 5y audit (a)**: descent uses only the *sound* half of the
contract.

This is a type-level separation: the body of
`PeelChain.contextual_admin_equiv_normalize_eq` (item 5s) takes a
`FrontierWordSoundNormalizer setup` argument, not a
`FrontierWordCompleteNormalizer setup` argument. Any
`CanNFObligations` registry can be projected to a sound normalizer
*without* discharging the `complete` field; this projection is the
witness. -/
def toSoundNormalizer : FrontierWordSoundNormalizer setup where
  NF := NF
  normalize := normalize
  sound := O.sound

/-- **Item 5y audit (b)**: equality detection requires the *complete*
half of the contract.

A `FrontierWordCompleteNormalizer` projection of a `CanNFObligations`
registry exists only because `complete` is supplied as a field.
Removing the `complete` field from the registry would make this
projection impossible — a type-level witness that 5t depends on
`complete` and not merely on `sound`. -/
def toCompleteNormalizer : FrontierWordCompleteNormalizer setup where
  toFrontierWordSoundNormalizer := O.toSoundNormalizer
  complete := O.complete

/-- **Item 5y audit (c) — non-circularity**: the soundness-side
descent (5s, against `O.toSoundNormalizer`) does **not** use the
`complete` field.

Stated as a definitional `rfl`: re-deriving 5s through the
`SoundNormalizer` projection produces the same equation as the direct
appeal to `O.sound`, regardless of whether `O.complete` is supplied.
Any change to `complete` cannot affect this equation — Lean enforces
this by structural projection. -/
theorem descent_uses_only_sound
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    PeelChain.contextual_admin_equiv_normalize_eq O.toSoundNormalizer h
      = O.sound (PeelChain.contextual_admin_equiv_word_stable h) :=
  rfl

/-- **Item 5y audit (d) — equality-detection-needs-completeness**:
the iff in 5t (`normalize_eq_iff_frontier_word_equiv`) is *exactly*
the pair `⟨complete, sound⟩` against the complete normalizer
projection.

Stated as a definitional `rfl`: removing `complete` would break the
forward direction of the iff. Lean enforces this by the projection
type signature. -/
theorem detection_uses_complete
    (w₁ w₂ : FrontierWord setup) :
    normalize_eq_iff_frontier_word_equiv O.toCompleteNormalizer w₁ w₂
      = ⟨O.complete, O.sound⟩ :=
  rfl

end CanNFObligations

/-! ### Manuscript-facing audit aliases -/

/-- **Manuscript-facing audit alias**: descent is sound-only.
Pointer to [`CanNFObligations.descent_uses_only_sound`]. -/
theorem theorem_descent_uses_only_sound_normalizer
    {NF : Type v} {normalize : FrontierWord setup → NF}
    (O : CanNFObligations setup NF normalize)
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    PeelChain.contextual_admin_equiv_normalize_eq O.toSoundNormalizer h
      = O.sound (PeelChain.contextual_admin_equiv_word_stable h) :=
  O.descent_uses_only_sound h

/-- **Manuscript-facing audit alias**: equality detection requires
completeness. Pointer to [`CanNFObligations.detection_uses_complete`]. -/
theorem theorem_detection_uses_complete_normalizer
    {NF : Type v} {normalize : FrontierWord setup → NF}
    (O : CanNFObligations setup NF normalize)
    (w₁ w₂ : FrontierWord setup) :
    normalize_eq_iff_frontier_word_equiv O.toCompleteNormalizer w₁ w₂
      = ⟨O.complete, O.sound⟩ :=
  O.detection_uses_complete w₁ w₂

/-
TEX ref: our_paper_draft.tex, label thm:normalization-completeness (L1420+)
Paper role: the CanNF normalization is complete — equal normal forms imply
  frontier-word equivalence; the final conclusion of the normalization package
Lean status: CONDITIONAL-FIELD-PROJECTION → projects O.complete field (M3)
  The paper's thm:normalization-completeness is not proved here;
  this theorem only unpacks the `complete` contract field of CanNFObligations.
  Renamed _from_obligations to prevent overclaim.
-/
/-- **`thm:normalization-completeness`** (conditional projection): canonical normal
form normalization is complete — IF the `CanNFObligations.complete` contract field
is inhabited.

This is NOT a paper-level proof: it only projects the `complete` field from the
`CanNFObligations` external contract structure (per `INV CanNF-Contract`). The
actual manuscript proof obligation (that the rewrite system satisfies completeness)
remains in the `CanNFObligations.complete` field and is unverified here.  

Status: CONDITIONAL-FIELD-PROJECTION -/
theorem normalization_completeness_from_obligations
    {setup : RewriteCalculusSetup.{u}}
    {NF : Type v} {normalize : FrontierWord setup → NF}
    (O : CanNFObligations setup NF normalize)
    {w₁ w₂ : FrontierWord setup}
    (h : normalize w₁ = normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  O.complete h

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
