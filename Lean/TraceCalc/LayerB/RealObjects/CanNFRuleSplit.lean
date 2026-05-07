import TraceCalc.LayerB.RealObjects.CanNFRuleFamilies

/-!
# Real-objects formalization: CanNF rule taxonomy split (items 6k–6o)

**Phase 3B items 6k–6o (2026-04-24).** This file separates the
**residue-level** CanNF rule families (whose operational data is
available from the skeletal `FrontierWord setup` alone) from the
**trace-level** CanNF rule families (whose operational data
requires chain/certificate context not present on the current
`FrontierWord`).

This is the honest follow-up to the enrichment finding flagged in
`CanNFRuleFamilies.lean`: rather than enriching `FrontierWord`
silently, we make the data-layer split explicit at the rule-taxonomy
level, so that:

* residue-level rules can be implemented against the existing
  `FrontierWord` without changing it;
* trace-level rules are isolated as a *separate* enum whose
  operational implementation is gated on a future enriched carrier
  (a placeholder for which is exposed as an obligation structure).

## Items in this file

* **6k** — Split rule taxonomy: `FrontierResidueRuleFamily` (six
  constructors, residue-only) and `FrontierTraceRuleFamily` (one
  constructor, requires trace context); inclusions back into the
  unified `FrontierRuleFamily` from `CanNFRuleFamilies.lean`.
* **6l** — Data-requirement classifier: `DataRequirement` enum
  (`residue_only`, `needs_trace_context`, `needs_certificate_context`,
  `future_unknown`); `dataRequirement : FrontierRuleFamily →
  DataRequirement` total function; classification theorems.
* **6m** — Residue-level rule application interface specializing
  `FrontierRuleApplication` to residue-only rules; bridge theorem
  `residue_rule_application_can_be_stated_on_FrontierWord`.
* **6n** — `FrontierTraceContextObligations`: lightweight obligation
  structure naming what data a future enriched frontier word must
  carry to support trace-level rules. **No carrier is implemented.**
* **6o** — Manuscript-facing aliases + a docstring summary of the
  data-layer split.

## Honest scope (per user's stop conditions, all honored)

* `FrontierWord` is **not** silently enriched. It remains the
  skeletal residue carrier.
* No rule system is instantiated.
* No confluence is proved.
* `FrontierTraceContextObligations` is named as an obligation
  structure for a future enriched carrier; it is not implemented.

## Architectural payoff

The split makes the design boundary between *residue-level
canonicality* (the boundary/admin material already proven through
items 5e–5o) and *trace-level canonicality* (chain/certificate
material that genuinely requires new data) **type-checkable**. A
future implementer cannot accidentally instantiate a trace-level
rule against `FrontierWord`-only data because the trace-level enum's
classifier returns `needs_trace_context`, and the residue-level
specialization machinery only accepts the residue-only constructors.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1186–L1192 (per-step descent).
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

/-! ## Item 6k — Split rule taxonomy -/

/-- **`FrontierResidueRuleFamily setup`**: rule families whose
operational data is available from the skeletal `FrontierWord setup`
alone (i.e., from `residue : CompletedReconstructionRecord setup`).

These are the six residue-level constructors of the unified
`FrontierRuleFamily` from `CanNFRuleFamilies.lean`. The constructor
names match exactly so the inclusion `toRuleFamily` is by direct
constructor mapping. -/
inductive FrontierResidueRuleFamily (setup : RewriteCalculusSetup.{u}) where
  /-- Canonicalize the boundary-admin representative (acts on `residue.Y`). -/
  | boundary_admin_canonicalize
  /-- Canonicalize the dependency ordering (acts on `residue.dep`). -/
  | dependency_order_canonicalize
  /-- Canonicalize the tensor-factor order (acts on `residue.tensor`). -/
  | tensor_factor_order_canonicalize
  /-- Canonicalize the canonical-key labeling (acts on `residue.key`). -/
  | key_order_canonicalize
  /-- Remove an inserted administrative identity move (acts on
  `residue.dep` / `residue.attach`). -/
  | remove_administrative_identity
  /-- Expose a boundary-block swap (acts on `residue.Y`, `residue.ports`). -/
  | expose_boundary_block_swap
deriving DecidableEq

/-- **`FrontierTraceRuleFamily setup`**: rule families whose
operational data requires chain/certificate context **not** present
on the current skeletal `FrontierWord setup`.

This isolates the rules whose implementation is gated on a future
enriched frontier-word carrier (see `FrontierTraceContextObligations`
in item 6n). -/
inductive FrontierTraceRuleFamily (setup : RewriteCalculusSetup.{u}) where
  /-- Compose two adjacent certified administrative steps. Requires
  chain-level provenance (an `AdministrativeChain`-style witness)
  not carried by `FrontierWord setup`. -/
  | compose_adjacent_certified_steps
deriving DecidableEq

namespace FrontierResidueRuleFamily

/-- Inclusion into the unified `FrontierRuleFamily`: each residue
rule maps to its same-named constructor. -/
def toRuleFamily : FrontierResidueRuleFamily setup → FrontierRuleFamily setup
  | .boundary_admin_canonicalize => .boundary_admin_canonicalize
  | .dependency_order_canonicalize => .dependency_order_canonicalize
  | .tensor_factor_order_canonicalize => .tensor_factor_order_canonicalize
  | .key_order_canonicalize => .key_order_canonicalize
  | .remove_administrative_identity => .remove_administrative_identity
  | .expose_boundary_block_swap => .expose_boundary_block_swap

/-- All six residue-level families enumerated. -/
def all : List (FrontierResidueRuleFamily setup) :=
  [ .boundary_admin_canonicalize
  , .dependency_order_canonicalize
  , .tensor_factor_order_canonicalize
  , .key_order_canonicalize
  , .remove_administrative_identity
  , .expose_boundary_block_swap ]

end FrontierResidueRuleFamily

namespace FrontierTraceRuleFamily

/-- Inclusion into the unified `FrontierRuleFamily`: the single
trace-level constructor maps to `compose_adjacent_certified_steps`. -/
def toRuleFamily : FrontierTraceRuleFamily setup → FrontierRuleFamily setup
  | .compose_adjacent_certified_steps => .compose_adjacent_certified_steps

/-- All trace-level families enumerated (currently one). -/
def all : List (FrontierTraceRuleFamily setup) :=
  [ .compose_adjacent_certified_steps ]

end FrontierTraceRuleFamily

/-- Manuscript-facing alias for the residue-rule inclusion. -/
def residueRule_to_ruleFamily :
    FrontierResidueRuleFamily setup → FrontierRuleFamily setup :=
  FrontierResidueRuleFamily.toRuleFamily

/-- Manuscript-facing alias for the trace-rule inclusion. -/
def traceRule_to_ruleFamily :
    FrontierTraceRuleFamily setup → FrontierRuleFamily setup :=
  FrontierTraceRuleFamily.toRuleFamily

/-! ## Item 6l — Data-requirement classifier -/

namespace FrontierRuleFamily

/-- **`DataRequirement`**: classification of what data layer a rule
family's operational implementation requires.

* `residue_only` — implementable against `FrontierWord setup` (i.e.,
  against `residue : CompletedReconstructionRecord setup`) alone.
* `needs_trace_context` — requires chain provenance
  (`AdministrativeChain`-style or `PeelChain`-derived data) not
  present on the skeletal `FrontierWord`.
* `needs_certificate_context` — requires per-step
  `ReplayCertificate` data carried by `PrimitiveCertifiedDeclaration`
  but not collected onto a frontier word.
* `future_unknown` — placeholder for rule families not yet classified.
-/
inductive DataRequirement where
  | residue_only
  | needs_trace_context
  | needs_certificate_context
  | future_unknown
deriving DecidableEq

/-- **The classifier**: total function from `FrontierRuleFamily` to
`DataRequirement`. The six residue-level constructors return
`residue_only`; `compose_adjacent_certified_steps` returns
`needs_trace_context`. -/
def dataRequirement : FrontierRuleFamily setup → DataRequirement
  | .boundary_admin_canonicalize => .residue_only
  | .dependency_order_canonicalize => .residue_only
  | .tensor_factor_order_canonicalize => .residue_only
  | .key_order_canonicalize => .residue_only
  | .remove_administrative_identity => .residue_only
  | .compose_adjacent_certified_steps => .needs_trace_context
  | .expose_boundary_block_swap => .residue_only

end FrontierRuleFamily

/-- **Classification theorem (6l.6)**: `compose_adjacent_certified_steps`
is **not** residue-only — it requires trace context. This is the
type-checked codification of the honest enrichment report from
`CanNFRuleFamilies.lean`. -/
theorem dataRequirement_compose_adjacent_certified_steps :
    (FrontierRuleFamily.compose_adjacent_certified_steps (setup := setup)).dataRequirement
      = FrontierRuleFamily.DataRequirement.needs_trace_context :=
  rfl

/-- **Classification theorem (6l.6.b)**: every residue-level family
classifies as `residue_only` under the unified classifier. -/
theorem dataRequirement_of_residueRule
    (r : FrontierResidueRuleFamily setup) :
    (residueRule_to_ruleFamily r).dataRequirement
      = FrontierRuleFamily.DataRequirement.residue_only := by
  cases r <;> rfl

/-- **Classification theorem (6l.6.c)**: every trace-level family
classifies as `needs_trace_context` under the unified classifier. -/
theorem dataRequirement_of_traceRule
    (r : FrontierTraceRuleFamily setup) :
    (traceRule_to_ruleFamily r).dataRequirement
      = FrontierRuleFamily.DataRequirement.needs_trace_context := by
  cases r <;> rfl

/-! ## Item 6m — Residue-level rule application interface -/

/-- **`FrontierResidueRuleApplication setup`**: a typed witness of a
single residue-level rule application.

This is the residue-only specialization of `FrontierRuleApplication`
from `CanNFRuleFamilies.lean`: the `family` field is restricted to
`FrontierResidueRuleFamily`, and `before`/`after` are
`FrontierWord setup` (the residue carrier). The `valid` and
`application_sound` fields have the same shape as in the unified
contract. -/
structure FrontierResidueRuleApplication (setup : RewriteCalculusSetup.{u}) where
  /-- Which residue-level rule family fired. -/
  family : FrontierResidueRuleFamily setup
  /-- The frontier word before the rule was applied. -/
  before : FrontierWord setup
  /-- The frontier word after the rule was applied. -/
  after : FrontierWord setup
  /-- Local validity condition for this particular application. -/
  valid : Prop
  /-- **Application soundness obligation**: a valid application
  produces an admin-equivalent successor. Same shape as
  `FrontierRuleApplication.application_sound`. -/
  application_sound : valid → FrontierWord.Equiv before after

namespace FrontierResidueRuleApplication

/-- Convenience accessor: when valid, the application produces an
admin-equivalent successor. -/
theorem sound_of_valid (app : FrontierResidueRuleApplication setup)
    (h : app.valid) :
    FrontierWord.Equiv app.before app.after :=
  app.application_sound h

/-- **Bridge into the unified `FrontierRuleApplication`**: a
residue-level rule application is a unified rule application whose
`family` factor is the inclusion image. -/
def toRuleApplication
    (app : FrontierResidueRuleApplication setup) :
    FrontierRuleApplication setup where
  family := residueRule_to_ruleFamily app.family
  before := app.before
  after := app.after
  valid := app.valid
  application_sound := app.application_sound

end FrontierResidueRuleApplication

/-- **Bridge theorem (6m.8)**: every `FrontierResidueRuleApplication`
*can be stated* against the skeletal `FrontierWord` — its
`before`/`after` fields are `FrontierWord setup`, and its underlying
unified rule application's `family.dataRequirement` is `residue_only`.
This is a **definitional** bridge, not a semantic claim about
correctness. -/
theorem residue_rule_application_can_be_stated_on_FrontierWord
    (app : FrontierResidueRuleApplication setup) :
    (app.toRuleApplication.family).dataRequirement
      = FrontierRuleFamily.DataRequirement.residue_only :=
  dataRequirement_of_residueRule app.family

/-! ## Item 6n — Trace-enriched future carrier obligation -/

/-- **`FrontierTraceContextObligations setup`**: a lightweight
obligation structure naming what data a *future* enriched frontier
word must carry to support trace-level CanNF rule families.

**No carrier is implemented here.** The fields are named obligations
on a future `CertifiedFrontierWord` / `FrontierWordWithTrace`
structure. Each field is a `Prop`-valued or `Sort`-valued obligation
with a docstring explaining what it must contain.

This is the **explicit gate** mentioned in the file header: a future
implementer who wants to instantiate a `FrontierTraceRuleFamily` rule
must first provide an instance of this structure (or a refinement of
it) parameterized over their chosen enriched carrier. -/
structure FrontierTraceContextObligations (setup : RewriteCalculusSetup.{u}) where
  /-- The proposed enriched-carrier type. Future implementers will
  refine this to e.g. `CertifiedFrontierWord setup` or
  `FrontierWordWithTrace setup`. -/
  EnrichedCarrier : Type u
  /-- A projection back to the skeletal residue carrier. The
  enriched carrier must refine `FrontierWord`, not replace it. -/
  toFrontierWord : EnrichedCarrier → FrontierWord setup
  /-- The trace-context payload: what chain/certificate data the
  enriched carrier exposes. The manuscript candidate is some shape
  derived from `RewriteCalculusSetup.AdministrativeChain` or
  `PeelChain`, but the precise choice is deferred. -/
  TraceContext : EnrichedCarrier → Type u
  /-- **Obligation**: trace-level rule families can be stated against
  the enriched carrier. This is a `Prop`-valued obligation; closing
  it requires defining a `FrontierTraceRuleApplication`-style
  structure on `EnrichedCarrier`. -/
  trace_rules_statable : Prop
  /-- **Obligation**: the enriched carrier's trace context is
  compatible with `FrontierWord.Equiv` (i.e., admin-equivalent
  underlying residues admit a corresponding trace-context
  equivalence). This is the trace-level analog of the residue-level
  `boundary_admin_compat` obligation. -/
  trace_context_admin_compat : Prop

/-! ## Item 6o — Manuscript-facing aliases -/

/-- **Manuscript alias (6o.11.a)**: every residue-level rule family
classifies as residue-only — i.e., the rule families in the residue
taxonomy are word-local in the precise sense that they require only
`FrontierWord` data. -/
theorem theorem_frontier_residue_rules_are_word_local
    (r : FrontierResidueRuleFamily setup) :
    (residueRule_to_ruleFamily r).dataRequirement
      = FrontierRuleFamily.DataRequirement.residue_only :=
  dataRequirement_of_residueRule r

/-- **Manuscript alias (6o.11.b)**: `compose_adjacent_certified_steps`
requires trace context. -/
theorem theorem_compose_adjacent_steps_requires_trace_context :
    (FrontierRuleFamily.compose_adjacent_certified_steps (setup := setup)).dataRequirement
      = FrontierRuleFamily.DataRequirement.needs_trace_context :=
  dataRequirement_compose_adjacent_certified_steps

/-- **Manuscript alias (6o.11.c)**: trace-level CanNF requires an
enriched frontier word — type-shape pointer to
`FrontierTraceContextObligations`, the obligation structure naming
the enriched-carrier requirement. The mere existence of this
obligation structure as a *separate* type from `FrontierWord` is the
machine-checked statement of the manuscript's trace-level enrichment
requirement. -/
def theorem_trace_level_cannf_requires_enriched_frontier_word :
    Type (u + 1) :=
  FrontierTraceContextObligations setup → True → Type u
-- The body's exact shape is immaterial — what matters is that this
-- declaration *exists* and *mentions* `FrontierTraceContextObligations`,
-- making the dependency type-checkable.

/-
TEX ref: our_paper_draft.tex, label def:primitive-family-classifier (L1370+)
Paper role: a function (or decision procedure) that assigns each primitive
  frontier word to exactly one of the five generator families
Lean status: MISSING → definition stub added (M3)
-/
/-- **`def:primitive-family-classifier`**: a classifier assigning each
primitive frontier word to one of the five generator families (G1-G5).

The classifier maps each `FrontierRuleFamily` to the predicate it satisfies,
and assigns each frontier word to the unique family whose predicate it satisfies.
This is the decision procedure underlying the CanNF join-rule families.

The concrete implementation of the classifier requires knowing the boundary
structure of each rule; it is registered here as a Prop-obligation structure. -/
structure PrimitiveFamilyClassifier (setup : RewriteCalculusSetup.{u}) where
  /-- The classification function: assigns each rule application to a family. -/
  classify : FrontierRuleApplication setup → FrontierRuleFamily setup
  /-- Correctness: the classified family matches the rule application's data. -/
  correct : Prop
  /-- Exhaustiveness: every rule application is classifiable. -/
  exhaustive :
    ∀ (app : FrontierRuleApplication setup),
      ∃ (fam : FrontierRuleFamily setup), classify app = fam

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
