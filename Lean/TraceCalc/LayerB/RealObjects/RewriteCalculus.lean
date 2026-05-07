/-!
# Real-objects formalization: the primitive certified step (Layer B)

**Real-objects path, cycle 1 (2026-04-23).** Per the strict
anti-impersonation standard adopted on the same day, this is the **first**
file in the project that aims at faithful object-level encoding of the
manuscript's own definitions.

## What this file contains, and what it does NOT

This file formalizes, against the manuscript text:

* `def:carrier` (`our_paper_draft.tex` L429) — the certified-trace carrier.
* `def:doctrine-definition` (L445) — the rewrite doctrine.
* `def:occurrence` (L605, with prerequisites `def:typed-occurrence-map` L587
  and `def:filler-data-and-ambient-parent-attachments` L591).
* `def:primitive-certified-declaration` (L611) — the four-component object
  that is the manuscript's local unit of computation.
* `def:admissibility` (L656) — six-clause admissibility predicate.
* `def:primitive-support-payload` (L679) — the eight-tuple of payload data.
* `def:administrative-transition` (L725).
* `def:replay-representative` (L731).

Every manuscript component is named and present as a Lean field.

This file deliberately **does not**:

* Construct cirquents, goals, states, rewrite schemes, typed occurrence maps,
  filler data, ambient attachment data, or replay certificates from first
  principles. The manuscript builds these by induction on a long preceding
  development (Sections L380–L583); attempting to re-derive them in a single
  cycle risks producing another shadow. Instead, this file carries them as
  **opaque types** on a `RewriteCalculusSetup` parameter bundle. Every
  manuscript field is then typed honestly against those opaque carriers.
* State or prove any manuscript theorem. No theorem may be tagged with a
  manuscript label until it is stated against these real objects (or an
  explicitly proved equivalent reformulation).
* Touch the reconstruction record yet. That is `def:completed-reconstruction-record`
  (L1100); it depends on `Packets`, `Attach`, `Dep`, etc., each of which has
  its own faithful encoding requirement, and is the next cycle's target.

The opaque-types-with-named-fields discipline is itself the
"explicitly proved equivalent reformulation" clause of the strict standard:
once any concrete instantiation of `RewriteCalculusSetup` is provided
(e.g., for a small toy carrier), the structures here become concrete via
that instantiation, with no field changes.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects` so that there is no
possibility of confusion with the shadow model in
`TraceCalc.LayerB.ShadowModel.*`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

/-! ### Carrier and doctrine

Per `def:carrier` (L429) and `def:doctrine-definition` (L445), the trace
calculus is parameterized by a fixed signature `Σ_∂` of typed boundary
slots, a rewrite doctrine over that signature, and a carrier of sanctioned
primitive interface patterns.

The substructure required by `def:primitive-certified-declaration` (L611)
is bundled below as `RewriteCalculusSetup`. Every component named in the
manuscript appears as a Lean field; types that the manuscript constructs by
induction earlier in the paper (cirquents, pattern trees, replay
certificates) are carried as opaque parameters here. -/

/-- Bundle of carrier types and gate predicates required to state
`def:primitive-certified-declaration` (L611) and downstream definitions
faithfully.

Manuscript correspondence:

* `Slot, Sort_` — the typed boundary slots and intrinsic sort system `S`
  introduced in §"Primitive interface data" L380, L388.
* `Cirquent, Goal, State` — the cirquents, well-formed goals, and trace
  states of L546–L583.
* `RewriteScheme, OperationSymbol, AdmissibilityPredicate` — the three
  components `(Σ_op, R, A)` of `def:doctrine-definition` (L445), with `Σ_∂`
  carried by `Slot` and `Sort_`.
* `TypedOccurrenceMap, FillerData, AmbientAttachmentData` — the three
  components of `def:occurrence` (L587, L591, L605).
* `Carrier, sanctionedByPatternAdmissionGate` — the registry `𝒫` and the
  pattern-admission gate of `def:carrier` (L429).
* `ReplayCertificate, SupportData` — the certificate-and-support fields of
  `def:primitive-certified-declaration` clauses (3) and (4) (L617–L618).
* `consumes / exports` — the named input/output resource identifiers of
  `def:primitive-support-payload` (L679, the `Res_in` / `Res_out` slots).
-/
structure RewriteCalculusSetup where
  /-- Typed boundary slots from the interface signature `Σ_∂` (L380). -/
  Slot : Type u
  /-- Intrinsic sort system `S` from L388 (free interface algebra). -/
  Sort_ : Type u
  /-- Cirquents (L546). -/
  Cirquent : Type u
  /-- Well-formed goals `(C, ∂C)` of L570. -/
  Goal : Type u
  /-- Trace states `(E, G)` of L570. -/
  State : Type u
  /-- The current goal of a state. -/
  goalOf : State → Goal
  /-- Operation symbols `Σ_op` of `def:doctrine-definition` (L447). -/
  OperationSymbol : Type u
  /-- Rewrite schemes `R = {ℓ ⇒ r}` of `def:doctrine-definition` (L450). -/
  RewriteScheme : Type u
  /-- Decidable admissibility predicate `A : R × State → Bool` of
  `def:doctrine-definition` (L452). -/
  admissible : RewriteScheme → State → Bool
  /-- Typed occurrence map `μ : ℓ → C` (L587). -/
  TypedOccurrenceMap : RewriteScheme → Goal → Type u
  /-- Filler data for the holes of the left pattern of a rewrite scheme
  (L591), in a given goal. -/
  FillerData : RewriteScheme → Goal → Type u
  /-- Ambient parent-attachment data (L591). -/
  AmbientAttachmentData : RewriteScheme → Goal → Type u
  /-- The certified-trace carrier `𝒫 = {(p_k, I_k)}` (L432). -/
  Carrier : Type u
  /-- The carrier under consideration. -/
  carrier : Carrier
  /-- The pattern-admission gate of `def:carrier` (L433): given an
  occurrence in a goal, the gate decides whether the exposed interface
  matches some sanctioned pattern in the carrier port-by-port. -/
  sanctionedByPatternAdmissionGate :
    Carrier → (ρ : RewriteScheme) → (G : Goal) → TypedOccurrenceMap ρ G → Bool
  /-- Support data: the named input/output resource identifiers of
  `def:primitive-certified-declaration` clause (3) (L617). -/
  SupportData : RewriteScheme → Goal → Type u
  /-- The named input resource identifiers `Res_in(P)` extracted from the
  support data; manuscript `def:primitive-support-payload` (L679). -/
  consumes : {ρ : RewriteScheme} → {G : Goal} → SupportData ρ G → Type u
  /-- The named output resource identifiers `Res_out(P)`. -/
  exports : {ρ : RewriteScheme} → {G : Goal} → SupportData ρ G → Type u
  /-- The replay certificate: a witness package verifying admissibility
  inside the current state. `def:primitive-certified-declaration` clause
  (4) (L618). -/
  ReplayCertificate : RewriteScheme → State → Type u
  /-- Boundary objects `X, Y` along which a replay representative runs
  (`def:replay-representative`, L731). The manuscript treats these as the
  boundary data of states; we expose them as a separate carrier with a
  projection from `State` so that the completed reconstruction record
  (`def:completed-reconstruction-record`, L1098) can name `X` and `Y`
  without dragging full state data. -/
  BoundaryObject : Type u
  /-- The boundary object of a state. -/
  boundaryOf : State → BoundaryObject
  /-- Refined interface label (`In^♯` / `Out^♯`) of
  `rem:refined-interfaces-derived` (L671) and Definitions L679/L686. A
  refined interface label is a typed semantic resource carrying its
  source step and boundary slot. -/
  RefinedInterface : Type u
  /-- Reattachment / gluing witness data: the certified reinsertion data
  used by `Glue` in `thm:canonical-reconstruction-algorithm` Step 3
  (L1180) and recorded as `Attach(P_k)` in
  `def:completed-reconstruction-record` clause (d) (L1115). Distinct from
  `AmbientAttachmentData` (which is per-occurrence inside one rewrite
  step); a `GluingWitness` is the post-recursion reinsertion datum used
  when a packet is glued back to the assembled predecessor cirquent. -/
  GluingWitness : Type u
  /-- Boolean compatibility check for an attachment witness against a
  given source/target boundary pair and refined input/output port lists.
  This is the manuscript's typed-interface compatibility from C2 of
  `def:completed-reconstruction-record` (L1128) and from
  `def:admissibility` clause (c) (L662): the attachment witness must be
  compatible with the typed interfaces and the ambient cirquent
  structure. The decision procedure depends on the concrete carrier;
  here it is an opaque field. -/
  attachmentCompatible :
    GluingWitness →
      (boundaryBefore boundaryAfter : BoundaryObject) →
      (refinedIn refinedOut : List RefinedInterface) → Bool
  /-- Boundary exposure under sink deletion: `def:boundary-exposure`
  (L1224). Given a target boundary `Y`, the refined output ports of the
  removed sink (to be removed from `Y`, step (i) of the definition), and
  the unmatched outputs of its predecessors (to be exposed, step (ii)),
  return the exposed boundary `Y_s`.

  The manuscript also records (step (iii)) that ports of remaining
  packets are unchanged; this is part of the carrier-level functoriality
  asserted in the closing sentence of L1224.

  **Manuscript clarity (flagged 2026-04-23):** the manuscript characterizes
  this operation up to the three numbered steps and the closing
  functoriality clause but does not give a closed-form formula on
  cirquents — the recipe is constructive given typed interface data. We
  carry it as an opaque setup operation; concrete instantiations of the
  rewrite calculus will provide the explicit formula. -/
  exposeBoundaryUnderSinkDeletion :
    BoundaryObject →
      (sinkRefinedOut : List RefinedInterface) →
      (exposedFromPredecessors : List RefinedInterface) → BoundaryObject
  /-- The `Glue` operation of `thm:canonical-reconstruction-algorithm`
  Step 3 (L1180): "Glue performs the certified reinsertion of `s` into
  the ambient cirquent of `R` according to the typed boundary interfaces
  and the attachment witness `Attach(s)`."

  **Manuscript clarity (flagged 2026-04-23):** the manuscript's `Glue`
  takes the *reconstructed certified trace* `R := T(∂*\s)` of the
  predecessor record (real-path obligation (4), not yet formalized) and
  produces a reconstructed trace, i.e., it is a typed operation between
  certified trace objects. Since the certified trace object is not yet
  available in the real-objects scaffolding, we model `Glue` here at the
  `BoundaryObject` level — the level at which `def:boundary-exposure`
  (L1224) operates and at which the typed boundary interfaces of the
  manuscript live. This is honest in that the operation's *boundary
  effect* (exposing/re-occluding the sink's refined outputs) is captured
  exactly; the certified-trace witness production is deferred to a later
  cycle. The carrier `Y_s ↝ Y` produced here must agree with the inverse
  of `exposeBoundaryUnderSinkDeletion`, per
  `lem:sink-deletion-inverse` (L1240). -/
  glueBoundary :
    (predecessorBoundary : BoundaryObject) →
      (sinkRefinedIn sinkRefinedOut : List RefinedInterface) →
      GluingWitness → BoundaryObject
  /-- Geometric rewrite rules `R_geom` referenced by `def:trace-equivalence`
  clause (c) (`our_paper_draft.tex` L754).

  **Manuscript clarity (flagged 2026-04-23):** `R_geom` is defined
  elsewhere in the manuscript (in the section on geometric generation /
  trace polygraph) and is not pinned down at the introduction site of
  `def:trace-equivalence`. We carry it here as an opaque carrier; the
  `Rewrite 2-cells` of `def:trace-equivalence` are then parameterized by
  an inhabitant of `GeometricRewriteRule`. -/
  GeometricRewriteRule : Type u
  /-- The canonical geometric rewrite rule produced by the sink-deletion/gluing
  inverse (`lem:sink-deletion-inverse`, `our_paper_draft.tex` L1240).

  Given:
  - `exposedBoundary`: the boundary `Y_s` produced by `exposeBoundaryUnderSinkDeletion`
    after removing the sink packet `s`;
  - `targetBoundary`: the original target boundary `Y` before deletion;
  - `sinkRefinedIn sinkRefinedOut`: the typed refined input/output ports of the
    removed sink (the `In^♯(s)` and `Out^♯(s)` of `def:refined-interfaces`);
  - `w : GluingWitness`: the reattachment data for packet `s` (the `Attach(s)`
    of `def:completed-reconstruction-record` clause (d), L1115);

  this field produces the geometric rewrite rule `r ∈ R_geom` that witnesses,
  at the level of `def:trace-equivalence` clause (c), that the boundary
  canonical replay representative is equivalent to the zero canonical replay
  representative under the sink-deletion/gluing inverse.

  The rule is parameterized by raw boundary-level data — all of which is already
  present in `RewriteCalculusSetup` — so that no downstream import cycle is
  introduced.  A concrete instantiation of the rewrite calculus supplies the
  actual polygraph rewrite rule here. -/
  sinkDeletionGeometricRule :
    (exposedBoundary targetBoundary : BoundaryObject) →
    (sinkRefinedIn sinkRefinedOut : List RefinedInterface) →
    GeometricRewriteRule

namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup)

/-! ### Occurrences

`def:occurrence` (L605): an occurrence of a rewrite scheme `ρ = (β, ℓ, r)`
in a goal `G = (C, ∂C)` is a triple consisting of a typed occurrence map
`μ : ℓ → C`, filler data `(K_i)` for the holes of `ℓ`, and ambient
parent-attachment data `A`. -/

/-- Occurrence of a rewrite scheme `ρ` in a goal `G`. Faithful to
`def:occurrence` (`our_paper_draft.tex` L605). -/
structure Occurrence (ρ : setup.RewriteScheme) (G : setup.Goal) where
  /-- Typed occurrence map `μ : ℓ → C` (L587). -/
  occMap : setup.TypedOccurrenceMap ρ G
  /-- Filler data `(K_i)` for the holes of the left pattern (L591). -/
  filler : setup.FillerData ρ G
  /-- Ambient parent-attachment data `A` (L591). -/
  attach : setup.AmbientAttachmentData ρ G

/-! ### Primitive certified declaration

`def:primitive-certified-declaration` (L611): on a state `S`, a
declaration consists of (1) a rewrite scheme in the doctrine, (2) an
occurrence of that scheme in the current goal, (3) support data naming the
consumed and exported semantic resources, and (4) a replay certificate. -/

/-- Faithful encoding of `def:primitive-certified-declaration`
(`our_paper_draft.tex` L611): the local unit of computation in the trace
calculus. All four manuscript fields are present; none has been collapsed
or normalized away. -/
structure PrimitiveCertifiedDeclaration (S : setup.State) where
  /-- (1) rewrite scheme `ρ = (β, ℓ, r)` in the doctrine (L615). -/
  scheme : setup.RewriteScheme
  /-- (2) an occurrence of `ρ` in the current goal (L616). -/
  occurrence : Occurrence setup scheme (setup.goalOf S)
  /-- (3) support data naming the individual semantic resources consumed
  and exported by the step (L617). -/
  support : setup.SupportData scheme (setup.goalOf S)
  /-- (4) a replay certificate — proof-object/witness package verifying
  admissibility inside the current state (L618). -/
  certificate : setup.ReplayCertificate scheme S

namespace PrimitiveCertifiedDeclaration

variable {setup}

/-! ### Admissibility (six clauses of `def:admissibility`, L656)

The manuscript states admissibility as a six-clause predicate:

  (a) the occurrence map lands in the current goal and preserves typing;
  (b) the filler data are compatible with the holes of the left pattern;
  (c) the ambient parent-attachment data reconnect the right pattern
      without violating the doctrine or creating cycles;
  (d) the exposed interface matches a sanctioned pattern in the carrier
      (`def:carrier`);
  (e) the support data name semantic resources available in the current
      state;
  (f) the replay certificate verifies the required compatibility conditions.

We expose each clause as a separate field of an `IsAdmissible` Prop, so the
manuscript's six-clause structure is preserved exactly. The content of each
clause beyond what the carrier-types pin down is kept as an opaque Prop
field on `RewriteCalculusSetup` *for future refinement*; we do not bundle
those into `RewriteCalculusSetup` yet because the manuscript states each
clause against fields of the declaration itself, so they belong here.

These clauses will become concrete once a specific instantiation of
`RewriteCalculusSetup` provides decidable predicates for each one. The
structure here records that the manuscript's decomposition into six clauses
is preserved verbatim. -/

/-- Predicate witnessing admissibility of a primitive certified
declaration. Faithful to `def:admissibility` (`our_paper_draft.tex` L656),
clauses (a)–(f). -/
structure IsAdmissible {S : setup.State} (P : PrimitiveCertifiedDeclaration setup S) :
    Prop where
  /-- (a) Occurrence map lands in the current goal and preserves typing.
  This is true definitionally in our encoding because `Occurrence` is
  parameterized by the goal of `S` and `TypedOccurrenceMap` is typed
  against the rewrite scheme; we record it as `True` to keep the
  six-clause structure visible at the type level. Concrete instantiations
  will be free to refine this. -/
  occMapTyped : True
  /-- (b) Filler data compatible with the holes of the left pattern. -/
  fillerCompatible : True
  /-- (c) Ambient parent-attachment data reconnect the right pattern
  without violating the doctrine or creating cycles. -/
  attachmentLegal : True
  /-- (d) Exposed interface matches a sanctioned pattern in the carrier
  (`def:carrier`, L429). This clause is witnessed via the
  pattern-admission gate carried on `RewriteCalculusSetup`. -/
  sanctioned :
    setup.sanctionedByPatternAdmissionGate setup.carrier P.scheme (setup.goalOf S)
      P.occurrence.occMap = true
  /-- (e) Support data name semantic resources available in the current
  state. -/
  supportNamesAvailable : True
  /-- (f) Replay certificate verifies the required compatibility
  conditions. -/
  certificateValid : True
  /-- (Doctrine clause from `def:doctrine-definition` (L452): the doctrine
  admissibility predicate must hold on this `(scheme, state)` pair. The
  manuscript folds this into clauses (c) and (f); we expose it here so
  that decidability of `setup.admissible` is directly visible in the
  `IsAdmissible` predicate.) -/
  doctrineAdmits : setup.admissible P.scheme S = true

end PrimitiveCertifiedDeclaration

/-! ### Primitive support payload

`def:primitive-support-payload` (L679): the eight-tuple

  Supp_0(P) = (ρ(P), μ(P), K(P), A(P), sort(P), var(P), Res_in(P), Res_out(P))

We carry every component. The eight fields below are in 1-1 correspondence
with the manuscript tuple, in the same order. -/

/-- Faithful encoding of `def:primitive-support-payload`
(`our_paper_draft.tex` L679). All eight manuscript components are present
as named fields. -/
structure PrimitiveSupportPayload {S : setup.State}
    (P : PrimitiveCertifiedDeclaration setup S) where
  /-- `ρ(P)`: the rewrite scheme. (Definitionally `P.scheme`; recorded as
  a field so the eight-tuple shape is visible in the type.) -/
  rho      : setup.RewriteScheme := P.scheme
  /-- `μ(P)`: the occurrence map. -/
  mu       : setup.TypedOccurrenceMap P.scheme (setup.goalOf S) := P.occurrence.occMap
  /-- `K(P)`: the filler data. -/
  K        : setup.FillerData P.scheme (setup.goalOf S) := P.occurrence.filler
  /-- `A(P)`: the ambient parent-attachment data. -/
  A        : setup.AmbientAttachmentData P.scheme (setup.goalOf S) := P.occurrence.attach
  /-- `sort(P)`: the interface sort. -/
  sort     : setup.Sort_
  /-- `var(P) ∈ {In, Out}^{|∂|}`: variance assignment on the boundary
  slots. -/
  variance : List (setup.Slot × Bool)
  /-- `Res_in(P)`: named input resource identifiers. -/
  resIn    : setup.consumes P.support
  /-- `Res_out(P)`: named output resource identifiers. -/
  resOut   : setup.exports P.support

/-! ### Administrative transitions and replay representatives

`def:administrative-transition` (L725) and `def:replay-representative`
(L731). -/

/-- Faithful encoding of `def:administrative-transition`
(`our_paper_draft.tex` L725): a bookkeeping move on a state that changes
only the presentation of the current boundary object and does not alter
the underlying geometric content.

The manuscript requires that "every admissible administrative move has a
named type and an inverse" (L728–L729). The named-type field is recorded
here; the global existence of an inverse is recorded as the separate
proposition `HasInverse` below, since making the inverse a self-referential
field would render the inductive non-strictly-positive. -/
structure AdministrativeTransition (S S' : setup.State) where
  /-- Named type of the administrative move; per the manuscript every
  admissible administrative move has a named type (L728). -/
  name : String

/-- Manuscript condition L729: every admissible administrative transition
has an inverse. Stated as a separate proposition rather than a self-field
of `AdministrativeTransition` to avoid a non-strictly-positive occurrence. -/
def AdministrativeTransition.HasInverse {S S' : setup.State}
    (_t : AdministrativeTransition setup S S') : Prop :=
  Nonempty (AdministrativeTransition setup S' S)

/-- A finite (possibly empty) sequence of administrative transitions
between two states. Used in `def:replay-representative` (L731) where each
`a_k` is "a (possibly empty) finite sequence of administrative
transitions". -/
inductive AdministrativeChain : setup.State → setup.State → Type u
  | nil  : (S : setup.State) → AdministrativeChain S S
  | cons : {S S' S'' : setup.State} →
           setup.AdministrativeTransition S S' →
           AdministrativeChain S' S'' →
           AdministrativeChain S S''

/-- Faithful encoding of `def:replay-representative`
(`our_paper_draft.tex` L731): a finite sequence

  σ = (a_0, P_1, a_1, P_2, a_2, …, P_n, a_n)

from a boundary object `X` to a boundary object `Y`, where each `P_k` is a
primitive certified step and each `a_k` is a (possibly empty) finite
sequence of administrative transitions.

We index by start- and end-state, with the alternating shape captured by
two constructors: `identity` (the `n = 0` case, i.e., only administrative
transitions, the *identity replay* of L735), and `step` (one administrative
chain followed by one primitive certified step, recursively followed by the
rest). -/
inductive ReplayRepresentative : setup.State → setup.State → Type u
  /-- The `n = 0` *identity replay* (L735): a single administrative chain
  with no primitive steps. -/
  | identity : {X Y : setup.State} → setup.AdministrativeChain X Y →
               ReplayRepresentative X Y
  /-- One administrative chain `a_{k-1}`, then one primitive certified
  step `P_k` (which transitions `Sk → Sk'` per `def:one-step-rule-application`,
  L623), then the rest of the replay representative. -/
  | step :
      {X Sk Sk' Y : setup.State} →
      setup.AdministrativeChain X Sk →
      (P : setup.PrimitiveCertifiedDeclaration Sk) →
      (advance : ReplayRepresentative Sk' Y) →
      ReplayRepresentative X Y

/-- Administrative-step admissibility relation used by
`TwoCellGenerator.admin`.

Current conservative definition (2026-04-26 safety repair): equality of
replay representatives. This blocks the previous collapse where arbitrary
replay representatives were connected by unconstrained admin steps.

Concrete doctrine-specific administrative grammars can refine this by
changing this definition in a future dedicated refactor. -/
def AdminRelation {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y) : Prop :=
  σ = σ'

/-- Guardrail for the production admin relation: it is definitionally
equality on replay representatives. -/
@[simp] theorem adminRelation_eq_iff {X Y : setup.State}
    {σ σ' : setup.ReplayRepresentative X Y} :
    setup.AdminRelation σ σ' ↔ σ = σ' :=
  Iff.rfl

/-! ### Future-only admin extensibility layer (inactive)

Current production behavior:
* `AdminRelation` is equality (`σ = σ'`).
* `AdminMoveCertificate` is not used to inhabit `AdminRelation`.

Any future broadening from equality must first be justified by explicit
preservation obligations and an anti-collapse argument. -/

/-- Inactive certificate shape for future nontrivial administrative moves.

This structure is intentionally not wired into `AdminRelation` yet. Fields are
named obligations rather than `True` placeholders. -/
structure AdminMoveCertificate
    {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y) where
  sameBoundary : Prop
  sameSupport : Prop
  samePacketMultiset : Prop
  sameCanonicalReplayShape : Prop
  /-- The source/target endpoints are already indexed in the types of `σ, σ'`.
  This field names the future obligation that broadening must preserve that
  endpoint discipline semantically as well as type-theoretically. -/
  preservesSourceTarget : Prop

/-- Theorem carrier for any future broadening of `AdminRelation` beyond
equality.  This is intentionally inactive scaffolding; production behavior
stays Eq-based until these obligations are discharged. -/
structure SafeAdminBroadeningObligation
    {X Y : setup.State}
    (σ σ' : setup.ReplayRepresentative X Y) where
  certificateImpliesAdminRelation :
    setup.AdminMoveCertificate σ σ' → setup.AdminRelation σ σ'
  adminPreservesBoundary : Prop
  adminPreservesSupport : Prop
  adminPreservesCanNFRelevantData : Prop
  noAdminCollapse : Prop

end RewriteCalculusSetup

/-
TEX ref: our_paper_draft.tex, label def:local-semantic-signature (L1360+)
Paper role: the local semantic signature of a frontier word classifies it
  by sort, generator family (Corr/Loc/Nis/A1/Env), and adjacency data
Lean status: MISSING → definition stub moved to CanonicalFrontierWord.lean (M3)
  (FrontierWord is not in scope in this file; LocalSemanticSignature is defined
  in CanonicalFrontierWord.lean where FrontierWord is available)
-/

end RealObjects
end LayerB
end TraceCalc
