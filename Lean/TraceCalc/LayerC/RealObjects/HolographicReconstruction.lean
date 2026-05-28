import TraceCalc.LayerB.RealObjects.CanNFRuleSplit

/-!
# Real-objects formalization: holographic reconstruction theorem schema (items 7a–7f)

**Phase 3B items 7a–7f (2026-04-24).** This file defines the
**holographic reconstruction theorem schema** in terms of the
current residue-level `FrontierWord` / CanNF interface, with an
**explicit, type-checked separation** between residue-level
canonicality (provable now, parametric in any
`FrontierWordSoundNormalizer` / `FrontierWordCompleteNormalizer`)
and trace-level canonicality (which requires a future enriched
carrier — see `FrontierTraceContextObligations` from 6n and the
holographic-trace pointer in 7d).

## Items in this file

* **7a** — `HolographicReconstructionData setup`: the data needed
  to lift the CanNF layer to a record-indexed reconstruction
  statement; carries `toFrontierWord :
  CompletedReconstructionRecord setup → FrontierWord setup` and
  `sound_on_records` (admin-equivalent records map to
  admin-equivalent frontier words). `identity` constructor wraps
  `R ↦ ⟨R⟩` (the residue-only canonical bridge).
* **7b** — CanNF-parametric reconstruction:
  `holographic_cannf_detects_record_equiv` (against a
  `FrontierWordCompleteNormalizer`, equality of normalized images
  is iff frontier-word equivalence) and
  `holographic_cannf_sound_on_records` (sound direction, against a
  `FrontierWordSoundNormalizer`).
* **7c** — Admin-compatible reconstruction:
  `contextual_admin_equiv_holographic_cannf_eq` consumes the
  genuinely-proved 5o `contextual_admin_equiv_word_stable`, NOT
  full replay.
* **7d** — Trace enrichment separation:
  `HolographicTraceEnrichmentObligations` reuses
  `FrontierTraceContextObligations` (since it already names the
  enriched-carrier requirement) plus an additional
  `holographic_lift` field projecting back to records;
  `theorem_holographic_trace_level_cannf_requires_enrichment`
  exposes the type-level dependency on
  `compose_adjacent_certified_steps.dataRequirement =
  needs_trace_context`.
* **7e** — Manuscript-facing aliases.

## Honest scope (per user's stop conditions, all honored)

* No CanNF is instantiated. All theorems are *parametric* in a
  supplied `FrontierWordSoundNormalizer` /
  `FrontierWordCompleteNormalizer`.
* No claim that trace-level CanNF is implemented. Trace-level
  reductions remain gated on
  `HolographicTraceEnrichmentObligations` /
  `FrontierTraceContextObligations`.
* Record equivalence is **never** derived from CanNF alone — the
  iff direction requires `N.complete`, which is exactly the
  `FrontierWordCompleteNormalizer` contract obligation.
* No proof routes through full `replay_stable` — the contextual
  reconstruction theorem consumes
  `PeelChain.contextual_admin_equiv_word_stable` (item 5o), which
  itself routes through the local two-step swap content.
* `FrontierWord` is **not** enriched.

## Architectural payoff

This file delivers what the user asked for in earlier sessions: a
**formal holographic reconstruction theorem in terms of CanNF**,
made precise by:

1. *Parametricity in the normalizer*: the theorem statement
   quantifies over `N : FrontierWord{Sound,Complete}Normalizer`,
   making the dependence on the *future* CanNF construction
   explicit at the type level. No "false closure" — the CanNF
   contract is a hypothesis, not a manufactured fact.
2. *Residue-level scope*: the conclusion is about
   `FrontierWord.Equiv` (i.e., `RecordStructEquiv BoundaryAdminEquiv`
   on residues), which is exactly what the residue-level CanNF can
   detect.
3. *Trace-level separation*: the trace-enrichment obligation
   structure is a *separate* type, mentioned by
   `theorem_holographic_trace_level_cannf_requires_enrichment` so
   the dependency is type-checkable.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the
  canonicality clause whose **holographic / record-indexed** form
  this file states.
* L1186–L1192 — per-step descent.
* L1224 (`def:boundary-exposure`) — the boundary exposure under
  which the residue-level canonicality is the relevant invariant.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain
open PeelChain
open PeelChain.FrontierObservation

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 7a — Holographic reconstruction data -/

/-- **`HolographicReconstructionData setup`**: the data needed to
lift the CanNF layer from `FrontierWord` to a record-indexed
reconstruction statement.

Carries:
* `toFrontierWord` — a function from completed reconstruction
  records to frontier words. The canonical residue-only choice
  (item 7a.2) is `R ↦ ⟨R⟩`, packaged as
  `HolographicReconstructionData.identity`. A future enriched
  carrier could refine this to attach trace context.
* `sound_on_records` — the admin-compatibility obligation:
  admin-equivalent records (`RecordStructEquiv BoundaryAdminEquiv`)
  map to admin-equivalent frontier words. For the `identity`
  constructor this is *immediate by definition* since
  `FrontierWord.Equiv ⟨R₁⟩ ⟨R₂⟩` is definitionally
  `RecordStructEquiv BoundaryAdminEquiv R₁ R₂`. -/
structure HolographicReconstructionData (setup : RewriteCalculusSetup.{u}) where
  /-- The reconstruction-to-frontier bridge. -/
  toFrontierWord : CompletedReconstructionRecord setup → FrontierWord setup
  /-- **Admin-compatibility obligation**: admin-equivalent records
  map to admin-equivalent frontier words. -/
  sound_on_records :
    ∀ {R₁ R₂ : CompletedReconstructionRecord setup},
      RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂ →
        FrontierWord.Equiv (toFrontierWord R₁) (toFrontierWord R₂)

namespace HolographicReconstructionData

/-- **The canonical residue-only reconstruction data**: wraps each
record `R` as the skeletal frontier word `⟨R⟩`.

This is **not final** if future trace-enriched data is needed —
holographic reconstruction at the trace level requires the enriched
carrier described in
`HolographicTraceEnrichmentObligations` (item 7d). -/
def identity : HolographicReconstructionData setup where
  toFrontierWord R := ⟨R⟩
  sound_on_records h := h
    -- Definitional: `FrontierWord.Equiv ⟨R₁⟩ ⟨R₂⟩` is by definition
    -- `RecordStructEquiv BoundaryAdminEquiv R₁ R₂` on `.residue`.

/-- The `identity` constructor's `toFrontierWord` reduces by `rfl`. -/
@[simp] theorem identity_toFrontierWord
    (R : CompletedReconstructionRecord setup) :
    (identity : HolographicReconstructionData setup).toFrontierWord R = ⟨R⟩ :=
  rfl

/-- Campaign-5 canonical reconstruction datum from completed records into the
current frontier object consumed downstream. This is the existing residue-only
bridge `R ↦ ⟨R⟩`, re-exposed under the reconstruction-facing name. -/
abbrev canonicalReconstruction_from_completedRecord :
    HolographicReconstructionData setup :=
  identity

/-- Campaign-5 canonical frontier reconstruction: the current canonical output
type for a completed record is `FrontierWord setup`. -/
def canonicalReconstruction_frontierWord
    (R : CompletedReconstructionRecord setup) : FrontierWord setup :=
  canonicalReconstruction_from_completedRecord.toFrontierWord R

@[simp] theorem canonicalReconstruction_frontierWord_eq
    (R : CompletedReconstructionRecord setup) :
    canonicalReconstruction_frontierWord R = FrontierWord.ofResidue R :=
  rfl

/-- Campaign-5 soundness: boundary-admin-equivalent completed records have the
same canonical reconstructed frontier word up to `FrontierWord.Equiv`. -/
theorem canonicalReconstruction_sound
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    FrontierWord.Equiv
      (canonicalReconstruction_frontierWord R₁)
      (canonicalReconstruction_frontierWord R₂) :=
  canonicalReconstruction_from_completedRecord.sound_on_records h

/-- Campaign-5 compatibility theorem: the canonical reconstruction respects the
completed-record equivalence relation currently used in the residue/frontier
layer, namely `RecordStructEquiv BoundaryAdminEquiv`. -/
theorem canonicalReconstruction_respects_completedRecord_equiv
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    FrontierWord.Equiv
      (canonicalReconstruction_frontierWord R₁)
      (canonicalReconstruction_frontierWord R₂) :=
  canonicalReconstruction_sound h

end HolographicReconstructionData

/-! ## Item 7b — CanNF-parametric reconstruction theorem -/

/-- **CanNF-parametric holographic reconstruction (complete
direction, item 7b.3)**: against any `FrontierWordCompleteNormalizer N`
and any `HolographicReconstructionData D`, equality of CanNF-images
is iff frontier-word equivalence.

Both directions are appeals to the supplied normalizer's contract:
the forward direction is `N.complete` (the **canonicality
obligation**), the backward direction is `N.sound`. **No CanNF is
constructed here** — the normalizer is a hypothesis. -/
theorem holographic_cannf_detects_record_equiv
    (D : HolographicReconstructionData setup)
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    N.normalize (D.toFrontierWord R₁) = N.normalize (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  ⟨N.complete, N.sound⟩

/-- **CanNF-parametric holographic reconstruction (sound direction
only, item 7b.4)**: against any `FrontierWordSoundNormalizer N` and
any `HolographicReconstructionData D`, admin-equivalent records
have equal CanNF-images.

This direction needs only the *sound* contract — no completeness is
assumed. Routes through `D.sound_on_records` (item 7a) +
`N.sound` (item 5r). -/
theorem holographic_cannf_sound_on_records
    (D : HolographicReconstructionData setup)
    (N : FrontierWordSoundNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    N.normalize (D.toFrontierWord R₁) = N.normalize (D.toFrontierWord R₂) :=
  N.sound (D.sound_on_records h)

/-! ## Item 7c — Admin-compatible reconstruction theorem -/

/-- **Contextual admin-equivalent holographic reconstruction (item
7c.5)**: contextually-admin-equivalent peel chains
(`PeelChain.ContextualAdminEquiv d c₁ c₂`) yield equal CanNF-images
of the canonical frontier word built from their depth-`d` frontier
observations, against any `FrontierWordSoundNormalizer`.

**The proof routes through the genuinely-proved 5o
`contextual_admin_equiv_word_stable` (which routes through the
local two-step swap content), NOT through full replay.** This
honors `INV AdminMove-Nonvacuity`. -/
theorem contextual_admin_equiv_holographic_cannf_eq
    (N : FrontierWordSoundNormalizer setup)
    {d : Nat}
    {R : CompletedReconstructionRecord setup}
    {c₁ c₂ : PeelChain R}
    (h : PeelChain.ContextualAdminEquiv d c₁ c₂) :
    N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  N.sound (PeelChain.contextual_admin_equiv_word_stable h)

/-! ## Item 7d — Trace enrichment separation -/

/-- **`HolographicTraceEnrichmentObligations setup`**: the trace-level
analog of `HolographicReconstructionData`, naming what data a
*future* trace-enriched holographic carrier must carry to support
trace-level CanNF rules.

This composes with `FrontierTraceContextObligations` (item 6n): the
holographic layer adds a `lift_from_record` projection from records
to the enriched carrier, plus an admin-compatibility obligation at
the enriched level. **No carrier is implemented here.** -/
structure HolographicTraceEnrichmentObligations
    (setup : RewriteCalculusSetup.{u}) where
  /-- The underlying trace-context obligations (item 6n) — names
  the enriched carrier and its trace-context payload without
  implementing it. -/
  traceContext : FrontierTraceContextObligations setup
  /-- Lift records into the enriched carrier. The future enriched
  carrier must support a record-indexed lift consistent with the
  residue-level `toFrontierWord` projection. -/
  lift_from_record :
    CompletedReconstructionRecord setup → traceContext.EnrichedCarrier
  /-- **Holographic admin-compat obligation at the enriched level**:
  admin-equivalent records lift to enriched-carrier elements whose
  underlying frontier words are admin-equivalent. This is the
  trace-level analog of `HolographicReconstructionData.sound_on_records`. -/
  lift_admin_compat : Prop

/-- **Item 7d.7 / Manuscript pointer 7e.11.c**:
`compose_adjacent_certified_steps` requires trace context — and
therefore any *holographic* CanNF claim that includes trace-level
reductions requires the enrichment described by
`HolographicTraceEnrichmentObligations`.

The proof body is exactly the residue/trace classifier from item 6l,
re-exported here under the holographic-layer name. -/
theorem theorem_holographic_trace_level_cannf_requires_enrichment :
    (FrontierRuleFamily.compose_adjacent_certified_steps (setup := setup)).dataRequirement
      = FrontierRuleFamily.DataRequirement.needs_trace_context :=
  dataRequirement_compose_adjacent_certified_steps

/-! ## Item 7e — Manuscript-facing aliases -/

/-- **Manuscript alias (7e.8.a)**: the holographic reconstruction
theorem is **parametric** in the supplied complete CanNF — the iff
between equal CanNF-images and admin-equivalent frontier words is
the contract iff of `FrontierWordCompleteNormalizer`. -/
theorem theorem_holographic_reconstruction_parametric_in_cannf
    (D : HolographicReconstructionData setup)
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    N.normalize (D.toFrontierWord R₁) = N.normalize (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  holographic_cannf_detects_record_equiv D N

/-- **Manuscript alias (7e.8.b)**: holographic reconstruction is
sound under contextual administrative equivalence of peel chains,
needing only a *sound* normalizer (no completeness). Routes through
`PeelChain.contextual_admin_equiv_word_stable` (item 5o), not full
replay. -/
theorem theorem_holographic_reconstruction_sound_under_admin_equiv
    (N : FrontierWordSoundNormalizer setup)
    {d : Nat}
    {R : CompletedReconstructionRecord setup}
    {c₁ c₂ : PeelChain R}
    (h : PeelChain.ContextualAdminEquiv d c₁ c₂) :
    N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
      = N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  contextual_admin_equiv_holographic_cannf_eq N h

/-- **Manuscript alias (7e.8.c)**: holographic reconstruction
*requires trace enrichment* for trace-level rule families. Pointer
to the residue/trace classifier — the type-checked statement that
`compose_adjacent_certified_steps` is `needs_trace_context`. -/
theorem theorem_holographic_reconstruction_requires_trace_enrichment_for_trace_rules :
    (FrontierRuleFamily.compose_adjacent_certified_steps (setup := setup)).dataRequirement
      = FrontierRuleFamily.DataRequirement.needs_trace_context :=
  theorem_holographic_trace_level_cannf_requires_enrichment

/-
TEX ref: our_paper_draft.tex, label rem:infty-holography (L1084)
Paper role: completed / infinity-level holography neighborhood
Lean status: OVERCLAIM -> M0 quarantined; `holographic_cannf_detects_record_equiv`
is retained only as a parametric CanNF support theorem.
-/
/-- **Quarantine marker (M0)**: the record-indexed CanNF theorem in this file
is parametric support, not unconditional completed / infinity holography.

What is proved here:
- `holographic_cannf_detects_record_equiv` is conditional on an explicit
  `FrontierWordCompleteNormalizer` hypothesis.
- `holographic_cannf_sound_on_records` and
  `contextual_admin_equiv_holographic_cannf_eq` are sound-direction support
  theorems only.

What is not proved here:
- unconditional completed holography;
- unconditional infinity-level holography;
- a concrete trace-enriched CanNF for trace-level rule families.

Downstream users must treat these declarations as support infrastructure for a
future closed reconstruction theorem, not as full manuscript closure. -/
def holographic_cannf_conditional_support_note : Prop :=
  ∀ {setup : RewriteCalculusSetup.{u}}
    (D : HolographicReconstructionData setup)
    (N : FrontierWordCompleteNormalizer.{u, u} setup)
    {R₁ R₂ : CompletedReconstructionRecord setup},
    N.normalize (D.toFrontierWord R₁) = N.normalize (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂)

theorem holographic_cannf_conditional_support_note_holds :
    holographic_cannf_conditional_support_note :=
  fun D N => holographic_cannf_detects_record_equiv D N

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
