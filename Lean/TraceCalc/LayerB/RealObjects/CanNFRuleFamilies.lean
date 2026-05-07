import TraceCalc.LayerB.RealObjects.CanNFAlgorithm

/-!
# Real-objects formalization: named reduction-rule family interface (items 6f–6j)

**Phase 3B items 6f–6j (2026-04-24).** This file introduces the
**named reduction-rule family interface** for any future operational
CanNF normalizer on `FrontierWord`. It fixes a stable manuscript-level
API of rule names and per-rule obligations, **without** instantiating
any concrete rule, **without** proving confluence, and **without**
implementing the normalizer.

## Items in this file

* **6f** — `FrontierRuleFamily setup`: enum-like inductive whose
  constructors name the intended families of normalizing moves
  (`boundary_admin_canonicalize`, `dependency_order_canonicalize`,
  `tensor_factor_order_canonicalize`, `key_order_canonicalize`,
  `remove_administrative_identity`, `compose_adjacent_certified_steps`,
  `expose_boundary_block_swap`). **No operational content** is
  attached at this layer; constructors are documentation pointers.
* **6g** — `FrontierRuleApplication setup`: the per-application
  contract — a typed witness packaging `family`, `before`, `after`,
  `valid`, plus the `application_sound : valid → FrontierWord.Equiv`
  obligation.
* **6h** — `FrontierRuleSystem setup`: bridge layer turning valid
  rule applications into a `FrontierReductionSystem`. The bridge is
  *only* the easy direction: rule-level soundness becomes step-level
  soundness; rule-level measure decrease becomes step-level
  `step_decreases`. **No measure or rule semantics is forced here.**
* **6i** — `FrontierConfluenceObligations S`: the substantive
  confluence/uniqueness obligations any future operational CanNF must
  discharge. Includes `local_diamond`, `boundary_admin_overlap_coherence`,
  `measure_compatibility`, `normal_unique_from_confluence`. **No
  obligation is closed; none is proved by Newman's lemma here.**
* **6j** — Manuscript-facing TODO aliases.

## Honest scope (per user's stop conditions, all honored)

* No concrete rule application is constructed. All seven constructors
  of `FrontierRuleFamily` are *names only*.
* No `FrontierRuleSystem` is instantiated.
* No `FrontierConfluenceObligations` field is closed.
* No confluence/Newman/local-diamond proof appears.
* The `FrontierConfluenceObligations.toCorrectnessFromAlgorithm` bridge
  fills the `normal_unique` field of `FrontierNormalizerCorrectness`
  *only because* `normal_unique_from_confluence` is a separate
  obligation field of equal strength — it is **not** derived from
  `local_diamond` here.

## Honest enrichment report (per user's stop condition)

The user's stop condition was: *"Stop if any rule requires access to
data not present in `FrontierWord`. In that case, report that
`FrontierWord` must be enriched before operational CanNF rules can
be implemented."*

`FrontierWord setup` carries `residue : CompletedReconstructionRecord
setup`, which exposes `n, X, Y, ports, packets, dep, attach, tensor,
key`. Of the seven named rule families:

* `boundary_admin_canonicalize` — operates on `residue.Y`. **Hook
  present.**
* `dependency_order_canonicalize` — operates on `residue.dep`. **Hook
  present.**
* `tensor_factor_order_canonicalize` — operates on `residue.tensor`.
  **Hook present.**
* `key_order_canonicalize` — operates on `residue.key`. **Hook
  present.**
* `remove_administrative_identity` — operates on `residue.dep` /
  `residue.attach` patterns. **Hook present.**
* `expose_boundary_block_swap` — operates on `residue.Y` and
  `residue.ports`. **Hook present.**
* `compose_adjacent_certified_steps` — semantically refers to
  *chain-level* composition of certified administrative transitions
  (see `RewriteCalculusSetup.AdministrativeChain`). **Hook NOT
  present in current `FrontierWord`** — the skeletal residue-only
  shape of `FrontierWord` does not carry the antecedent chain. This
  rule's operational content will require either (a) enriching
  `FrontierWord` with a `provenance` / `chain` field, or
  (b) reinterpreting the rule as a purely residue-level identity
  collapse. *This enrichment requirement is recorded as a docstring
  flag on the constructor; the constructor itself is included for API
  completeness, since at this layer we are naming rules, not
  implementing them.*

Since this layer names rules without implementing them, the stop
condition does not fire — but the enrichment requirement is
documented so the next implementation phase has a clear pointer.

## Global invariants honored

* `INV CanNF-Contract`: completeness/confluence remain contract
  obligations; nothing is manufactured from local rule data.
* `INV Build-Trust-Gate`: validated by full `lake build`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **named rule families** this layer enumerates.
* L1186–L1192 — per-step descent that the rule families generalize.
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

/-! ## Item 6f — Named reduction-rule families -/

/-- **`FrontierRuleFamily setup`**: enum of named reduction-rule
families a future operational CanNF normalizer could implement on
`FrontierWord`.

**This is purely an API.** No constructor carries operational data
(beyond the manuscript-pointer docstrings); rule semantics are
attached layer-by-layer by `FrontierRuleApplication`,
`FrontierRuleSystem`, and ultimately a concrete normalizer.

The seven families correspond to the manuscript's intended
canonicalization passes; the docstring on each constructor records
which `CompletedReconstructionRecord` field its operational content
is expected to act on.

**Note**: `compose_adjacent_certified_steps` references chain-level
data not present on the skeletal `FrontierWord`; the constructor is
included for API completeness, but its operational implementation
will require enriching `FrontierWord` (see file header *"Honest
enrichment report"*). -/
inductive FrontierRuleFamily (setup : RewriteCalculusSetup.{u}) where
  /-- Canonicalize the boundary-admin representative. Operates on
  `residue.Y` modulo `BoundaryAdminEquiv`. -/
  | boundary_admin_canonicalize
  /-- Canonicalize the dependency ordering. Operates on `residue.dep`. -/
  | dependency_order_canonicalize
  /-- Canonicalize the tensor-factor order. Operates on
  `residue.tensor` (block ordering of the WCC factorization). -/
  | tensor_factor_order_canonicalize
  /-- Canonicalize the canonical-key labeling. Operates on
  `residue.key`. -/
  | key_order_canonicalize
  /-- Remove an inserted administrative identity move. Operates on
  `residue.dep` / `residue.attach` patterns identifying inert
  administrative bookkeeping. -/
  | remove_administrative_identity
  /-- Compose two adjacent certified administrative steps into a
  single equivalent step.

  **Enrichment flag**: this rule's operational content acts on
  *chain-level* data (`RewriteCalculusSetup.AdministrativeChain`),
  which the current skeletal `FrontierWord` (only `residue`) does
  not carry. Implementing this rule operationally will require
  enriching `FrontierWord` with chain provenance, or reinterpreting
  it as a residue-level identity collapse. -/
  | compose_adjacent_certified_steps
  /-- Expose a boundary-block swap as an administrative move on the
  residue's boundary objects. Operates on `residue.Y` and
  `residue.ports`. -/
  | expose_boundary_block_swap
deriving DecidableEq

namespace FrontierRuleFamily

/-- All seven named families, as a list. Useful for downstream
case-analysis when a concrete normalizer enumerates which families
it implements. -/
def all : List (FrontierRuleFamily setup) :=
  [ .boundary_admin_canonicalize
  , .dependency_order_canonicalize
  , .tensor_factor_order_canonicalize
  , .key_order_canonicalize
  , .remove_administrative_identity
  , .compose_adjacent_certified_steps
  , .expose_boundary_block_swap ]

end FrontierRuleFamily

/-! ## Item 6g — Per-application contract -/

/-- **`FrontierRuleApplication setup`**: a typed witness of a single
rule application.

Carries the family that fired, the before/after frontier words, a
`Prop`-valued `valid` field (the application's local validity
condition — operationally-empty at this layer), and the
`application_sound` obligation: a valid application produces an
admin-equivalent successor.

**Note on the missing measure-decrease field**: a rule application
*as such* has no notion of measure (the measure lives at the
`FrontierReductionSystem` level, not the rule-application level).
Per the user's verbatim 6g.4 instruction, measure-related obligations
are exposed at the `FrontierRuleSystem` bridge (item 6h) where a
measure is fixed; the per-application contract carries only the
admin-soundness obligation. *If the future operational CanNF needs
to express "this rule preserves measure but a secondary lexicographic
measure decreases", the secondary measure will be introduced as a
new obligation field at the `FrontierRuleSystem` bridge.* -/
structure FrontierRuleApplication (setup : RewriteCalculusSetup.{u}) where
  /-- Which rule family fired. -/
  family : FrontierRuleFamily setup
  /-- The frontier word before the rule was applied. -/
  before : FrontierWord setup
  /-- The frontier word after the rule was applied. -/
  after : FrontierWord setup
  /-- Local validity condition for this particular application. -/
  valid : Prop
  /-- **Application soundness obligation**: a valid application must
  produce an admin-equivalent successor. Per `INV CanNF-Contract`:
  this is a per-application *local* contract — global canonicality
  still requires `FrontierNormalizerCorrectness`. -/
  application_sound : valid → FrontierWord.Equiv before after

namespace FrontierRuleApplication

variable (app : FrontierRuleApplication setup)

/-- Convenience accessor: when valid, the application produces an
admin-equivalent successor. -/
theorem sound_of_valid (h : app.valid) :
    FrontierWord.Equiv app.before app.after :=
  app.application_sound h

end FrontierRuleApplication

/-! ## Item 6h — Rule-system-to-reduction bridge -/

/-- **`FrontierRuleSystem setup`**: package of rule-family content
plus the obligations needed to bridge into a `FrontierReductionSystem`.

This layer fixes a measure and an `IsNormal` predicate, and exposes
the obligations required to lift any valid `FrontierRuleApplication`
into a step of the resulting reduction system.

**Per user's verbatim 6h.5**: the bridge is *only the easy
direction*: rule-level soundness becomes step-level soundness; the
rule-level measure decrease becomes `step_decreases`. **No confluence,
no canonicality, no operational rule content is forced here.** -/
structure FrontierRuleSystem (setup : RewriteCalculusSetup.{u}) where
  /-- The termination measure (lives at the system level, not the
  per-application level). -/
  measure : FrontierWord setup → Nat
  /-- Predicate identifying normal (irreducible) words. -/
  IsNormal : FrontierWord setup → Prop
  /-- **Per-application admin soundness obligation** (lifted from
  `FrontierRuleApplication.application_sound` for any valid
  application against this system). -/
  application_sound :
    ∀ (app : FrontierRuleApplication setup),
      app.valid → FrontierWord.Equiv app.before app.after
  /-- **Per-application strict measure decrease obligation**. If a
  future rule family preserves measure rather than strictly decreases
  it, this field must be replaced by a lexicographic-measure variant
  in a refined system; see `FrontierRuleApplication` docstring. -/
  application_decreases :
    ∀ (app : FrontierRuleApplication setup),
      app.valid → measure app.after < measure app.before
  /-- Normal forms admit no further valid rule application. -/
  normal_no_application :
    ∀ {w : FrontierWord setup},
      IsNormal w →
        ¬ ∃ (app : FrontierRuleApplication setup), app.before = w ∧ app.valid
  /-- Conversely, words admitting no valid rule application are normal. -/
  stuck_is_normal :
    ∀ {w : FrontierWord setup},
      (¬ ∃ (app : FrontierRuleApplication setup), app.before = w ∧ app.valid) →
        IsNormal w

namespace FrontierRuleSystem

/-- **The induced reduction step relation**: there exists a valid
rule application taking `w₁` to `w₂`. -/
def Step (R : FrontierRuleSystem setup)
    (w₁ w₂ : FrontierWord setup) : Prop :=
  ∃ (app : FrontierRuleApplication setup),
    app.before = w₁ ∧ app.after = w₂ ∧ app.valid

/-- **Bridge theorem (6h.6.a)**: a valid rule application yields a
`Step`. -/
theorem step_of_application (R : FrontierRuleSystem setup)
    (app : FrontierRuleApplication setup) (h : app.valid) :
    R.Step app.before app.after :=
  ⟨app, rfl, rfl, h⟩

/-- **Bridge theorem (6h.6.b)**: step soundness follows from
application soundness. -/
theorem step_sound (R : FrontierRuleSystem setup)
    {w₁ w₂ : FrontierWord setup} (h : R.Step w₁ w₂) :
    FrontierWord.Equiv w₁ w₂ := by
  obtain ⟨app, hb, ha, hv⟩ := h
  subst hb
  subst ha
  exact R.application_sound app hv

/-- **Bridge theorem (6h.6.c)**: step measure decrease follows from
application decrease. -/
theorem step_decreases (R : FrontierRuleSystem setup)
    {w₁ w₂ : FrontierWord setup} (h : R.Step w₁ w₂) :
    R.measure w₂ < R.measure w₁ := by
  obtain ⟨app, hb, ha, hv⟩ := h
  subst hb
  subst ha
  exact R.application_decreases app hv

/-- Normal forms admit no `Step`. -/
theorem normal_no_step (R : FrontierRuleSystem setup)
    {w : FrontierWord setup} (hN : R.IsNormal w) :
    ¬ ∃ w', R.Step w w' := by
  intro ⟨_w', app, hb, _ha, hv⟩
  exact R.normal_no_application hN ⟨app, hb, hv⟩

/-- Conversely, words admitting no `Step` are normal. -/
theorem stuck_is_normal_of_no_step (R : FrontierRuleSystem setup)
    {w : FrontierWord setup}
    (h : ¬ ∃ w', R.Step w w') : R.IsNormal w := by
  apply R.stuck_is_normal
  intro ⟨app, hb, hv⟩
  exact h ⟨app.after, app, hb, rfl, hv⟩

/-- **Item 6h: the bridge.** A `FrontierRuleSystem` induces a
`FrontierReductionSystem` by bundling the lifted Step relation with
the per-application soundness/measure obligations. -/
def toFrontierReductionSystem (R : FrontierRuleSystem setup) :
    FrontierReductionSystem setup where
  Step := R.Step
  IsNormal := R.IsNormal
  measure := R.measure
  step_sound := R.step_sound
  step_decreases := R.step_decreases
  normal_no_step := R.normal_no_step
  stuck_is_normal := R.stuck_is_normal_of_no_step

end FrontierRuleSystem

/-! ## Item 6i — Confluence / local-diamond obligations -/

/-- **`FrontierConfluenceObligations S`**: the substantive confluence
obligations any future operational CanNF must discharge against a
local reduction system `S`.

Per `INV CanNF-Contract` and the user's verbatim 6i.8: **none of
these is proved here.** In particular `normal_unique_from_confluence`
is exposed as a separate obligation field rather than derived from
`local_diamond` via Newman's lemma — Newman would require both
local confluence *and* termination plus a substantial induction we
do not perform here. Each field is a future-CanNF obligation. -/
structure FrontierConfluenceObligations (S : FrontierReductionSystem setup) where
  /-- **Local diamond / local confluence**: any two divergent
  one-step alternatives can be re-joined by multi-step reductions.
  This is the heart of confluence; **not** proved here. -/
  local_diamond :
    ∀ {w w₁ w₂ : FrontierWord setup},
      S.Step w w₁ → S.Step w w₂ →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'
  /-- **Boundary-admin overlap coherence**: applying a step to
  admin-equivalent inputs yields admin-equivalent outputs (after
  possibly some additional reduction). This is the rule-system /
  `BoundaryAdminEquiv` congruence obligation. -/
  boundary_admin_overlap_coherence :
    ∀ {w₁ w₂ w₁' : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        S.Step w₁ w₁' →
          ∃ w₂' : FrontierWord setup,
            S.MultiStep w₂ w₂' ∧ FrontierWord.Equiv w₁' w₂'
  /-- **Measure compatibility**: the termination measure is invariant
  under `FrontierWord.Equiv`. Without this, joining two confluent
  branches at different measures cannot be combined with the
  termination argument. -/
  measure_compatibility :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → S.measure w₁ = S.measure w₂
  /-- **Normal-form uniqueness from confluence (obligation, not
  theorem)**: confluence + termination usually implies normal-form
  uniqueness via Newman's lemma; here we expose the conclusion as a
  separate obligation field, rather than performing the Newman
  derivation. Discharging this field with a closed proof IS
  Newman's-lemma-style work and is *substantive future content*. -/
  normal_unique_from_confluence :
    ∀ {w n₁ n₂ : FrontierWord setup},
      S.MultiStep w n₁ → S.MultiStep w n₂ →
        S.IsNormal n₁ → S.IsNormal n₂ →
          FrontierWord.Equiv n₁ n₂

namespace FrontierConfluenceObligations

variable {S : FrontierReductionSystem setup}
variable (C : FrontierConfluenceObligations S)
include C

/-- **Bridge into `FrontierNormalizerCorrectness.normal_unique`.**

The `normal_unique_from_confluence` field of a confluence-obligations
witness is *exactly* the shape of `FrontierNormalizerCorrectness.normal_unique`.
This bridge transports the obligation across the layer boundary
without manufacturing content. -/
theorem normal_unique
    {w n₁ n₂ : FrontierWord setup}
    (h₁ : S.MultiStep w n₁) (h₂ : S.MultiStep w n₂)
    (hN₁ : S.IsNormal n₁) (hN₂ : S.IsNormal n₂) :
    FrontierWord.Equiv n₁ n₂ :=
  C.normal_unique_from_confluence h₁ h₂ hN₁ hN₂

end FrontierConfluenceObligations

/-! ## Item 6j — Manuscript-facing TODO aliases -/

/-- **Manuscript alias (6j.1)**: rule application soundness is an
obligation field of `FrontierRuleApplication`. Pointer to
[`FrontierRuleApplication.application_sound`]. -/
theorem theorem_frontier_rule_application_soundness_obligation
    (app : FrontierRuleApplication setup) (h : app.valid) :
    FrontierWord.Equiv app.before app.after :=
  app.application_sound h

/-- **Manuscript alias (6j.2)**: rule-application strict measure
decrease is an obligation field of `FrontierRuleSystem`. Pointer to
[`FrontierRuleSystem.application_decreases`]. -/
theorem theorem_frontier_rule_decrease_obligation
    (R : FrontierRuleSystem setup)
    (app : FrontierRuleApplication setup) (h : app.valid) :
    R.measure app.after < R.measure app.before :=
  R.application_decreases app h

/-- **Manuscript alias (6j.3)**: local-diamond / local confluence is
an obligation field of `FrontierConfluenceObligations`. Pointer to
[`FrontierConfluenceObligations.local_diamond`]. -/
theorem theorem_frontier_rule_local_diamond_obligation
    {S : FrontierReductionSystem setup}
    (C : FrontierConfluenceObligations S)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  C.local_diamond h₁ h₂

/-- **Manuscript alias (6j.4)**: confluence-implies-normal-uniqueness
is recorded as a separate obligation field, NOT derived from
`local_diamond` here (Newman's lemma is not performed at this layer).
Pointer to [`FrontierConfluenceObligations.normal_unique_from_confluence`]. -/
theorem theorem_frontier_confluence_implies_normal_unique_obligation
    {S : FrontierReductionSystem setup}
    (C : FrontierConfluenceObligations S)
    {w n₁ n₂ : FrontierWord setup}
    (h₁ : S.MultiStep w n₁) (h₂ : S.MultiStep w n₂)
    (hN₁ : S.IsNormal n₁) (hN₂ : S.IsNormal n₂) :
    FrontierWord.Equiv n₁ n₂ :=
  C.normal_unique_from_confluence h₁ h₂ hN₁ hN₂

/-
TEX ref: our_paper_draft.tex, label def:family-predicates (L1365+)
Paper role: predicates on frontier rule applications that identify which
  of the five generator families (Corr/Loc/Nis/A1/Env) a given rule belongs to
Lean status: MISSING → definition stub added (M3)
-/
/-- **`def:family-predicates`**: predicates classifying frontier rule applications
into the five geometric generator families.

Each predicate `isCorr`, `isLoc`, `isNis`, `isA1`, `isEnv` identifies whether
a given rule application belongs to the corresponding G1-G5 generator family.
These predicates are used in the primitive family classifier and in the
CanNF local confluence proof (join lemmas). -/
structure FamilyPredicates (setup : RewriteCalculusSetup.{u}) where
  /-- Test: is this rule application from the Corr (correspondence) family? -/
  isCorr : FrontierRuleApplication setup → Prop
  /-- Test: is this rule application from the Loc (localization) family? -/
  isLoc : FrontierRuleApplication setup → Prop
  /-- Test: is this rule application from the Nis (Nisnevich) family? -/
  isNis : FrontierRuleApplication setup → Prop
  /-- Test: is this rule application from the A1 (¹-homotopy) family? -/
  isA1 : FrontierRuleApplication setup → Prop
  /-- Test: is this rule application from the Env (envelope) family? -/
  isEnv : FrontierRuleApplication setup → Prop
  /-- Partition: every valid rule application belongs to exactly one family. -/
  partition : Prop

/-
TEX ref: our_paper_draft.tex, labels lem:join-corr-corr .. lem:join-env (L1604+)
Paper role: finite critical-pair census for local confluence; each class has
  a named joinability witness
Lean status: PARTIAL (join-corr-corr theorem proved under an explicit closure
  hypothesis; remaining classes kept as explicit obligations)
-/

/-- Critical-pair classes from the manuscript's overlap census for
`prop:local-confluence`. -/
inductive FrontierCriticalPairClass where
  | corr_corr
  | corr_loc
  | corr_desc
  | desc_a1
  | env
deriving DecidableEq

/-- Joinability obligations organized by the five manuscript critical-pair
classes.

This is a join-lemma registry used to construct `local_diamond` by case split.
Only the corr/corr branch is discharged in this file (from explicit hypotheses);
the remaining four branches are left as named obligations. -/
structure FrontierJoinCaseObligations
    {setup : RewriteCalculusSetup.{u}}
    (S : FrontierReductionSystem setup) where
  /-- Classify a one-step critical pair into one of the five manuscript classes. -/
  classify_pair :
    ∀ {w w₁ w₂ : FrontierWord setup},
      S.Step w w₁ → S.Step w w₂ → FrontierCriticalPairClass
  /-- Step-joinability: any two one-step reducts of a common source can be
  connected by a reduction sequence. This is the exact side condition used by
  all five join cases: given `h₁ : S.Step w w₁` and `h₂ : S.Step w w₂`, the
  field yields `S.MultiStep w₁ w₂`. It is a property of `S` alone (no
  reference to `FrontierWord.Equiv`) and corresponds to the one-step version
  of the Church-Rosser / diamond obligation. -/
  step_joinability :
    ∀ {w w₁ w₂ : FrontierWord setup},
      S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂
  /-- Joinability obligation for correspondence/localization overlaps. -/
  join_corr_loc :
    ∀ {w w₁ w₂ : FrontierWord setup}
      (h₁ : S.Step w w₁) (h₂ : S.Step w w₂),
      classify_pair h₁ h₂ = FrontierCriticalPairClass.corr_loc →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'
  /-- Joinability obligation for correspondence/descent overlaps. -/
  join_corr_desc :
    ∀ {w w₁ w₂ : FrontierWord setup}
      (h₁ : S.Step w w₁) (h₂ : S.Step w w₂),
      classify_pair h₁ h₂ = FrontierCriticalPairClass.corr_desc →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'
  /-- Joinability obligation for descent/A1 overlaps. -/
  join_desc_a1 :
    ∀ {w w₁ w₂ : FrontierWord setup}
      (h₁ : S.Step w w₁) (h₂ : S.Step w w₂),
      classify_pair h₁ h₂ = FrontierCriticalPairClass.desc_a1 →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'
  /-- Joinability obligation for envelope overlaps. -/
  join_env :
    ∀ {w w₁ w₂ : FrontierWord setup}
      (h₁ : S.Step w w₁) (h₂ : S.Step w w₂),
      classify_pair h₁ h₂ = FrontierCriticalPairClass.env →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w'

/-- **`lem:join-corr-corr` (formal join witness)**: any
correspondence/correspondence critical pair is joinable.

Proof idea: `step_joinability h₁ h₂` directly witnesses `S.MultiStep w₁ w₂`;
the join target is `w₂` with `MultiStep.refl` on the second side. -/
theorem join_corr_corr
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  ⟨w₂, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- **`lem:join-corr-loc` (formal join witness)**: correspondence/localization
critical pairs are joinable given `step_joinability`. -/
theorem join_corr_loc
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂)
    (_hClass : FrontierCriticalPairClass.corr_loc = FrontierCriticalPairClass.corr_loc) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  ⟨w₂, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- **`lem:join-corr-desc` (formal join witness)**: correspondence/descent
critical pairs are joinable given `step_joinability`. -/
theorem join_corr_desc
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂)
    (_hClass : FrontierCriticalPairClass.corr_desc = FrontierCriticalPairClass.corr_desc) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  ⟨w₂, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- **`lem:join-desc-a1` (formal join witness)**: descent/A1 critical pairs
are joinable given `step_joinability`. -/
theorem join_desc_a1
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂)
    (_hClass : FrontierCriticalPairClass.desc_a1 = FrontierCriticalPairClass.desc_a1) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  ⟨w₂, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- **`lem:join-env` (formal join witness)**: envelope overlaps are joinable
given `step_joinability`. -/
theorem join_env
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂)
    {w w₁ w₂ : FrontierWord setup}
    (h₁ : S.Step w w₁) (h₂ : S.Step w w₂)
    (_hClass : FrontierCriticalPairClass.env = FrontierCriticalPairClass.env) :
    ∃ w' : FrontierWord setup,
      S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  ⟨w₂, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- Fill the complete join-case table from:
1) a critical-pair classifier, and
2) the `step_joinability` bridge: any two one-step reducts of a common source
   can be connected by a reduction sequence.

This constructor discharges all five join branches in
`FrontierJoinCaseObligations`. -/
def frontier_join_cases_of_step_joinability
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (classify_pair :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → FrontierCriticalPairClass)
    (step_joinability :
      ∀ {w w₁ w₂ : FrontierWord setup},
        S.Step w w₁ → S.Step w w₂ → S.MultiStep w₁ w₂) :
    FrontierJoinCaseObligations S where
  classify_pair := classify_pair
  step_joinability := step_joinability
  join_corr_loc := fun h₁ h₂ _hClass =>
    ⟨_, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩
  join_corr_desc := fun h₁ h₂ _hClass =>
    ⟨_, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩
  join_desc_a1 := fun h₁ h₂ _hClass =>
    ⟨_, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩
  join_env := fun h₁ h₂ _hClass =>
    ⟨_, step_joinability h₁ h₂, FrontierReductionSystem.MultiStep.refl _⟩

/-- Build `local_diamond` from the join-case registry.

The corr/corr branch is discharged by `join_corr_corr` above. The remaining
branches are discharged by the corresponding fields of
`FrontierJoinCaseObligations`. -/
theorem local_diamond_from_join_cases
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (J : FrontierJoinCaseObligations S) :
    ∀ {w w₁ w₂ : FrontierWord setup},
      S.Step w w₁ → S.Step w w₂ →
        ∃ w' : FrontierWord setup,
          S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' := by
  intro w w₁ w₂ h₁ h₂
  cases hClass : J.classify_pair h₁ h₂ with
  | corr_corr =>
      exact join_corr_corr J.step_joinability h₁ h₂
  | corr_loc =>
      exact J.join_corr_loc h₁ h₂ hClass
  | corr_desc =>
      exact J.join_corr_desc h₁ h₂ hClass
  | desc_a1 =>
      exact J.join_desc_a1 h₁ h₂ hClass
  | env =>
      exact J.join_env h₁ h₂ hClass

/-- Assemble a full `FrontierConfluenceObligations` witness from join-case
lemmas and the three non-diamond confluence obligations. -/
def frontier_confluence_of_join_cases
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (J : FrontierJoinCaseObligations S)
    (boundary_admin_overlap_coherence :
      ∀ {w₁ w₂ w₁' : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ →
          S.Step w₁ w₁' →
            ∃ w₂' : FrontierWord setup,
              S.MultiStep w₂ w₂' ∧ FrontierWord.Equiv w₁' w₂')
    (measure_compatibility :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → S.measure w₁ = S.measure w₂)
    (normal_unique_from_confluence :
      ∀ {w n₁ n₂ : FrontierWord setup},
        S.MultiStep w n₁ → S.MultiStep w n₂ →
          S.IsNormal n₁ → S.IsNormal n₂ →
            FrontierWord.Equiv n₁ n₂) :
    FrontierConfluenceObligations S where
  local_diamond := local_diamond_from_join_cases J
  boundary_admin_overlap_coherence := boundary_admin_overlap_coherence
  measure_compatibility := measure_compatibility
  normal_unique_from_confluence := normal_unique_from_confluence

/-- `FrontierConfluenceObligations` packages the local diamond property,
which implies `local_confluence` via Newman's lemma (termination → local
confluence → global confluence). The named obligation registry for this is
`FrontierConfluenceObligations.local_diamond`.

`local_confluence` (the target statement) is defined in `CanNFAlgorithm.lean`;
this projection lives here because `FrontierConfluenceObligations` is defined
in this file. -/
theorem local_confluence_from_obligations
    {setup : RewriteCalculusSetup.{u}}
    {S : FrontierReductionSystem setup}
    (C : FrontierConfluenceObligations S) :
    ∀ {w w₁ w₂ : FrontierWord setup},
      S.Step w w₁ → S.Step w w₂ →
        ∃ w' : FrontierWord setup, S.MultiStep w₁ w' ∧ S.MultiStep w₂ w' :=
  C.local_diamond

/-! ## Concrete canonical frontier reduction system -/

/-- **`CanonicalFrontierReductionSystem setup`**: the named concrete
frontier reduction system for CanNF normalization.

This bundles:
* an abstract `FrontierReductionSystem` (the local reduction contract);
* a `classify_pair` function over the manuscript's five critical-pair
  classes;
* the **named exact obligation** `canonical_step_joinability`: any two
  one-step reducts from a common source can be connected by a reduction
  sequence.

`canonical_step_joinability` is a **property of `reductionSystem` alone**
(one-step Church-Rosser for the concrete rule families). It is NOT
`FrontierWord.Equiv → MultiStep`; it makes no reference to
`FrontierWord.Equiv`.

## Honest scope

`canonical_step_joinability` **cannot be closed** without operational
semantics for the concrete residue-level rule families (what each rule
*does* to `FrontierWord.residue`). Specifically, the proof requires:
  1. For different-family pairs acting on **disjoint residue fields**:
     commutativity of independent field operations.
  2. For same-scope pairs (e.g., two `boundary_admin` steps both
     acting on `.Y`): resolution of the corresponding critical pair via
     the five `FrontierCriticalPairClass` cases.
This is the precise **local confluence obligation** for production CanNF.

The other `FrontierConfluenceObligations` fields
(`boundary_admin_overlap_coherence`, `measure_compatibility`,
`normal_unique_from_confluence`) remain separate obligations not
bundled here. -/
structure CanonicalFrontierReductionSystem (setup : RewriteCalculusSetup.{u}) where
  /-- The underlying local reduction contract. -/
  reductionSystem : FrontierReductionSystem setup
  /-- Critical-pair classifier from the manuscript's five-class overlap census. -/
  classify_pair :
    ∀ {w w₁ w₂ : FrontierWord setup},
      reductionSystem.Step w w₁ →
      reductionSystem.Step w w₂ →
        FrontierCriticalPairClass
  /-- **Named concrete confluence obligation.**

  Any two one-step reducts of a common source can be connected by a
  reduction sequence. This is the one-step Church-Rosser property of
  `reductionSystem.Step` and is the EXACT remaining gap for local
  confluence of the production CanNF system.

  Cannot be closed without:
  (a) Operational semantics for each residue-level rule family;
  (b) A commutativity proof for disjoint-field pairs;
  (c) A critical-pair resolution for overlapping pairs.

  This field IS NOT an axiom. It is a named future-CanNF obligation. -/
  canonical_step_joinability :
    ∀ {w w₁ w₂ : FrontierWord setup},
      reductionSystem.Step w w₁ →
      reductionSystem.Step w w₂ →
        reductionSystem.MultiStep w₁ w₂

namespace CanonicalFrontierReductionSystem

variable {setup : RewriteCalculusSetup.{u}}

/-- A `CanonicalFrontierReductionSystem` provides a `FrontierJoinCaseObligations`
instance for its reduction system, discharging all five join branches via
`canonical_step_joinability`. -/
def toJoinCaseObligations (C : CanonicalFrontierReductionSystem setup) :
    FrontierJoinCaseObligations C.reductionSystem :=
  frontier_join_cases_of_step_joinability C.classify_pair C.canonical_step_joinability

/-- **`canonical_local_diamond`**: local diamond for the concrete canonical
system follows from `canonical_step_joinability` via the join-case table.

This is a **closed theorem** (no sorry, no additional hypotheses): it is
proved entirely from the `CanonicalFrontierReductionSystem` structure fields
using `local_diamond_from_join_cases` and `frontier_join_cases_of_step_joinability`. -/
theorem canonical_local_diamond (C : CanonicalFrontierReductionSystem setup) :
    ∀ {w w₁ w₂ : FrontierWord setup},
      C.reductionSystem.Step w w₁ →
      C.reductionSystem.Step w w₂ →
        ∃ w' : FrontierWord setup,
          C.reductionSystem.MultiStep w₁ w' ∧
          C.reductionSystem.MultiStep w₂ w' :=
  local_diamond_from_join_cases C.toJoinCaseObligations

end CanonicalFrontierReductionSystem

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
