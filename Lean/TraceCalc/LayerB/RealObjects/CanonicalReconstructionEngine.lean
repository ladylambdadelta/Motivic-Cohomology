import TraceCalc.LayerC.RealObjects.CanonicalReconstructionEngine

/-! Compatibility shim: the implementation moved to LayerC because it is a
derived reconstruction-engine layer built on LayerB foundations. -/

/- Retired copied implementation kept below only as historical context. The
live compatibility surface for this module is the LayerC import above.

import TraceCalc.LayerB.RealObjects.PeelChain
import TraceCalc.LayerB.RealObjects.ContextualAdminEquiv
import TraceCalc.LayerB.RealObjects.CanonicalFrontierWord
import TraceCalc.LayerB.RealObjects.HolographicReconstruction
import TraceCalc.LayerB.RealObjects.Replay
import TraceCalc.LayerB.RealObjects.CanonicalNormalForm
import TraceCalc.LayerB.RealObjects.CanNFProductionSystem

/-!
# Real-objects formalization: canonical reconstruction engine (items 3–10)

**Phase 3B, items 3–10 (2026-05-??).** This file packages the main
combinatorial theorem-carrier for canonical reconstruction. It bundles
the following manuscript ingredients into one core structure:

* `CanonicalReconstructionEngine` — the full evidence package:
  existing proved results plus a closed complete normalizer field.

## Items packaged

* **(A) Canonical sink selection** (items 3–4, manuscript L1180 Step 1):
  `canonicalSink_isSink`, `canonicalSink_unique`.
* **(B) Peel descent termination** (item 5, L1180 Step 1):
  `PeelChain.iterated_peel_descent` — peel strictly decreases `n`.
* **(C) Peel chain existence and canonicality** (item 6):
  `PeelChain.canonicalPeelChain` and its completion/canonicality lemmas,
  giving an intrinsic witness built from `canonicalSink` at every step.
* **(D) Canonical frontier word** (item 7, L1180 Step 2):
  `canonicalFrontierWord` + `contextual_admin_equiv_word_stable`
  (administrative invariance, item 5o).
* **(E) Replay / reattachment correctness** (item 8, L1180 Step 3):
  `replay_recordEquiv` (any chain replays to an equivalent record),
  `replay_stable` (any two chains on the same record give equivalent
  replay results).
* **(F) Holographic reconstruction data** (item 9):
  `HolographicReconstructionData.identity` instantiation.
* **(G) CanNF-facing equality theorem** (item 10, L1180 final clause):
  `holographic_cannf_detects_record_equiv`, parametric in a complete
  normalizer. Correctness direction requires `FrontierWordCompleteNormalizer`
  as an explicit hypothesis — never manufactured from frontier-equivalence
  machinery (`INV CanNF-Contract`).
* **(H) Closed complete normalizer** — currently instantiated by the
  semantic quotient normalizer from `CanonicalNormalForm.lean`.

## Honest scope

* The default closed constructor uses a semantic quotient normalizer.
* A computational upgrade path is provided by
  `CanonicalReconstructionEngine.ofComputationalCanNF`.
* `replay_stable` relies on `replay_recordEquiv`; it does NOT assert that
  canonical chains are literally equal, only that they replay to equivalent
  records.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause covered by items (A)–(G) above.
* L1186–L1192 — per-step descent (item B).
* L1224 (`def:boundary-exposure`) — boundary exposure under which
  residue-level canonicality is the relevant invariant.
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

/-! ### Main engine

The engine packages together:
* the proved canonical-peel infrastructure (A)–(G),
* an explicit pointer to the contract obligation (H),
* an `ofCurrentDevelopment` constructor that fills all proved fields
  from the already-green LayerB theorems. -/

/-- Main combinatorial theorem-carrier for canonical reconstruction
(`thm:canonical-reconstruction-algorithm`, `our_paper_draft.tex` L1180).

This structure bundles the key proved results of the Phase 3B canonical
reconstruction development together with a concrete closed normalizer for
CanNF completeness. It is designed so that:

1. Every field is filled in `ofCurrentDevelopment` from an existing
   theorem in a green LayerB file (no `sorry`, `admit`, or `:= True`).
2. Field **(H)** carries a `FrontierWordCompleteNormalizer` — the closed
   concrete normalizer from `CanonicalNormalForm.lean`.
3. CanNF-facing equality is stated *parametrically* in a supplied
   `FrontierWordCompleteNormalizer`, enforcing the contract boundary.

**Fields A–H are all inhabited by `ofClosedCanNF`.**
-/
structure CanonicalReconstructionEngine (setup : RewriteCalculusSetup.{u}) where
  /-- **(A1)** The canonical sink is a sink: `canonicalSink_isSink`. -/
  canonical_sink_isSink :
      ∀ (R : CompletedReconstructionRecord setup) (h : 0 < R.n),
        R.IsSink (canonicalSink R h)

  /-- **(A2)** The canonical sink has maximal key-position among sinks:
  `canonicalSink_pos_max`. -/
  canonical_sink_pos_max :
      ∀ (R : CompletedReconstructionRecord setup) (h : 0 < R.n)
        {s : Fin R.n} (_hs : R.IsSink s),
        R.key.pos s ≤ R.key.pos (canonicalSink R h)

  /-- **(B)** Iterated peel descent: the peel chain for any completed record
  has length equal to `R.n`, certifying that the dependency DAG is finite
  and acyclic. -/
  iterated_peel_descent :
      ∀ (R : CompletedReconstructionRecord setup) (c : PeelChain R),
        c.length = R.n

  /-- **(C1)** Peel chain existence: every completed record admits
  a completing peel chain, witnessed here by the canonical chain. -/
  peel_chain_exists :
      ∀ (R : CompletedReconstructionRecord setup) (_ : R.IsCompleted),
        Σ' (c : PeelChain R), c.Completes

  /-- **(C2)** Canonical peel chain existence: the canonical chain (always
  peeling at `canonicalSink`) exists and completes. -/
  canonical_chain_completes :
      ∀ (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted),
        (canonicalPeelChain R hC).Completes

  /-- **(C3)** Canonicality: the canonical peel chain is intrinsically
  canonical (every step uses `canonicalSink`). -/
  canonical_chain_isCanonical :
      ∀ (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted),
        (canonicalPeelChain R hC).IsCanonical

  /-- **(D)** Administrative invariance of the canonical frontier word
  (item 5o, `contextual_admin_equiv_word_stable`): contextually
  admin-equivalent chains yield frontier-word-equivalent canonical frontier
  words at every depth. -/
  canonical_word_admin_stable :
      ∀ {R : CompletedReconstructionRecord setup} {d : Nat}
        {c₁ c₂ : PeelChain R}
        (_ : ContextualAdminEquiv d c₁ c₂),
        FrontierWord.Equiv
          (canonicalFrontierWord (FrontierObservation.ofChain c₁ d))
          (canonicalFrontierWord (FrontierObservation.ofChain c₂ d))

  /-- **(E1)** Replay correctness: replay of any peel chain gives a record
  equivalent to the original (`replay_recordEquiv`). -/
  replay_recordEquiv :
      ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
        RecordEquiv (PeelChain.replay c) R

  /-- **(E2)** Replay stability: any two peel chains over the same record
  give replay-equivalent results (`replay_stable`). This is the manuscript's
  "any valid descent arrives at the same completed reconstruction up to record
  equivalence" clause of `thm:canonical-reconstruction-algorithm`. -/
  replay_stable :
      ∀ {R : CompletedReconstructionRecord setup} (c c' : PeelChain R),
        RecordEquiv (PeelChain.replay c) (PeelChain.replay c')

  /-- **(F)** Holographic reconstruction data: the residue-indexed bridge
  from completed records to frontier words. Instantiated here by the identity
  bridge `R ↦ ⟨R⟩` (`HolographicReconstructionData.identity`). -/
  holographic_data : HolographicReconstructionData setup

  /-- **(G1)** CanNF detects record equivalence (completeness direction),
  parametric in a `FrontierWordCompleteNormalizer`.

  Under a complete normalizer, normalized equality of the frontier-word
  images of two records is *equivalent* to frontier-word equivalence
  (which in turn is `RecordStructEquiv BoundaryAdminEquiv`).
  This direction requires `N.complete` and is thus gated on the contract
  obligation `canNF_normalizer`. -/
  cannf_detects_record_equiv :
      ∀ (N : FrontierWordCompleteNormalizer setup)
        (holo : HolographicReconstructionData setup)
        {R₁ R₂ : CompletedReconstructionRecord setup},
        N.normalize (holo.toFrontierWord R₁) = N.normalize (holo.toFrontierWord R₂) ↔
          FrontierWord.Equiv (holo.toFrontierWord R₁) (holo.toFrontierWord R₂)

  /-- **(G2)** Admin equivalence → same CanNF (sound direction), parametric in
  a `FrontierWordSoundNormalizer`. No contract obligation required — soundness
  follows from `contextual_admin_equiv_word_stable` (item 5o). -/
  cannf_sound_under_admin_equiv :
      ∀ (N : FrontierWordSoundNormalizer setup)
        (_ : HolographicReconstructionData setup)
        {R₁ : CompletedReconstructionRecord setup} {_R₂ : CompletedReconstructionRecord setup}
        (d : Nat) (c₁ c₂ : PeelChain R₁)
        (_hequiv : ContextualAdminEquiv d c₁ c₂),
        N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d)) =
          N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d))

  /-- **(H) Concrete complete normalizer** (closed CanNF contract,
  `INV CanNF-Contract`):

  Carries the `FrontierWordCompleteNormalizer` whose `complete` field is the
  manuscript's CanNF completeness theorem.

  Populated by `semanticQuotientFrontierWordCompleteNormalizer` in
  `ofClosedCanNF`.
  Can also be supplied explicitly via `ofCurrentDevelopment` during development. -/
  canNF_normalizer : FrontierWordCompleteNormalizer setup

namespace CanonicalReconstructionEngine

/-! ### The `ofCurrentDevelopment` constructor

Fills fields **(A)–(G)** from already-proved LayerB theorems.
Field **(H)** is left as an explicit hypothesis to be supplied by the user.

The constructor name follows the convention established in
`InternalManuscriptTargets.lean` (`CertifiedTraceCompositionTarget.ofCurrentDevelopment`).
-/

/-- Construct a `CanonicalReconstructionEngine` from the current LayerB
development, providing an explicit `FrontierWordCompleteNormalizer` for
the CanNF completeness contract (field H).

All fields **(A)–(G)** are discharged by existing proved theorems in green
LayerB files. Field **(H)** receives the concrete normalizer. -/
noncomputable def ofCurrentDevelopment
    (canNF_norm : FrontierWordCompleteNormalizer setup) :
    CanonicalReconstructionEngine setup where
  -- (A1) canonicalSink_isSink lives in CanonicalSink.lean
  canonical_sink_isSink R h := canonicalSink_isSink R h
  -- (A2) canonicalSink_pos_max lives in CanonicalSink.lean
  canonical_sink_pos_max := fun R h {_s} hs => canonicalSink_pos_max R h hs
  -- (B) PeelChain.length_eq lives in PeelChain.lean
  iterated_peel_descent _R c := PeelChain.length_eq c
  -- (C1) canonicalPeelChain + canonicalPeelChain_completes live in PeelChain.lean
  peel_chain_exists R hC :=
    ⟨PeelChain.canonicalPeelChain R hC, PeelChain.canonicalPeelChain_completes R hC⟩
  -- (C2) canonicalPeelChain_completes lives in PeelChain.lean
  canonical_chain_completes R hC := PeelChain.canonicalPeelChain_completes R hC
  -- (C3) canonicalPeelChain_isCanonical lives in PeelChain.lean
  canonical_chain_isCanonical R hC := PeelChain.canonicalPeelChain_isCanonical R hC
  -- (D) contextual_admin_equiv_word_stable lives in CanonicalFrontierWord.lean (item 5o)
  canonical_word_admin_stable h := PeelChain.contextual_admin_equiv_word_stable h
  -- (E1) replay_recordEquiv lives in Replay.lean
  replay_recordEquiv c := PeelChain.replay_recordEquiv c
  -- (E2) replay_stable lives in Replay.lean
  replay_stable c c' := PeelChain.replay_stable c c'
  -- (F) HolographicReconstructionData.identity lives in HolographicReconstruction.lean
  holographic_data := HolographicReconstructionData.identity
  -- (G1) holographic_cannf_detects_record_equiv lives in HolographicReconstruction.lean
  cannf_detects_record_equiv N holo {_R₁} {_R₂} :=
    holographic_cannf_detects_record_equiv holo N
  -- (G2) contextual_admin_equiv_holographic_cannf_eq lives in HolographicReconstruction.lean
  cannf_sound_under_admin_equiv := fun N _holo {_R₁} {_R₂} _d _c₁ _c₂ hequiv =>
    contextual_admin_equiv_holographic_cannf_eq N hequiv
  -- (H) Closed concrete normalizer
  canNF_normalizer := canNF_norm

/-- **Fully closed constructor**: all fields **(A)–(H)** are discharged
from existing proved theorems. No external obligation required.

Field **(H)** is filled by the semantic quotient normalizer
`semanticQuotientFrontierWordCompleteNormalizer` from
`CanonicalNormalForm.lean` (extensional closure, not the executable CanNF
algorithm). -/
noncomputable def ofClosedCanNF : CanonicalReconstructionEngine setup :=
  ofCurrentDevelopment semanticQuotientFrontierWordCompleteNormalizer

/-- **Computational upgrade constructor**.

Given a proof-relevant `ComputationalFrontierNormalizer` (which carries a
`Type`-level `NormalizationTrace`, decidable code, canonical projection, etc.)
this constructor feeds its extensional contract
(`N.toFrontierWordCompleteNormalizer`) into the engine's H field.

This is the upgrade path from `ofClosedCanNF` (semantic quotient closure) to
an executable CanNF algorithm. -/
noncomputable def ofComputationalCanNF
    (N : ComputationalFrontierNormalizer setup) :
    CanonicalReconstructionEngine setup :=
  ofCurrentDevelopment (computational_to_quotient_complete (setup := setup) N)

/-- Concrete production-side upgrade constructor.

This packages the fully constructive production CanNF closure directly into the
canonical reconstruction engine, using the proof-relevant computational
normalizer assembled from the concrete production data. -/
noncomputable def ofConcreteProductionCanNFData
    (B       : BoundaryAdminCanonicalizeData setup)
    (Dep     : DependencyOrderCanonicalizeData setup)
    (Tensor  : TensorFactorOrderCanonicalizeData setup)
    (Key     : KeyOrderCanonicalizeData setup)
    (Remove  : AdministrativeIdentityRemovalData setup)
    (Compose : AdjacentCertifiedStepCompositionData setup)
    (Expose  : BoundaryBlockSwapExposureData setup)
    (C : ProductionSchemaOperationalSideConditions
           (productionFamilySpecs_allConcreteOrConditional
             B Dep Tensor Key Remove Compose Expose))
    (JP   : ProductionJoinEnvPrimitive
              (productionFrontierRuleSystem_from_spec
                (productionSchemaOperationalSpec_concrete
                  B Dep Tensor Key Remove Compose Expose C)))
    (BC   : BoundaryAdminCanonicalizeCongr B)
    (TC   : TensorFactorOrderCanonicalizeUniqueData Tensor)
    (KC   : KeyOrderCanonicalizeUniqueData Key)
    (EOSort : CanNFProductionExternalOutSortData B Dep Tensor Key
                (productionSchemaOperationalSpec_concrete
                  B Dep Tensor Key Remove Compose Expose C)) :
    CanonicalReconstructionEngine setup :=
  ofComputationalCanNF <|
    productionComputationalFrontierNormalizer_from_concrete_data
      B Dep Tensor Key Remove Compose Expose C JP BC TC KC EOSort

/-! ### Downstream consequences

The following lemmas extract key conclusions from a
`CanonicalReconstructionEngine`. They are used by downstream manuscript
theorem carriers (ProofSpine, ManuscriptSpineTargets). -/

/-- From a `CanonicalReconstructionEngine`, for any completed record `R`,
the canonical peel chain completes and every chain replays to `R` up to
record equivalence. -/
theorem canonical_replay_equiv (eng : CanonicalReconstructionEngine setup)
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    RecordEquiv (PeelChain.replay (canonicalPeelChain R hC)) R :=
  eng.replay_recordEquiv (canonicalPeelChain R hC)

/-- Any two completed records whose holographic CanNF images agree (under a
complete normalizer) satisfy frontier-word equivalence. This is the record-level
CanNF detection theorem derived from the engine. -/
theorem record_equiv_iff_cannf_eq (eng : CanonicalReconstructionEngine setup)
    (N : FrontierWordCompleteNormalizer setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    N.normalize (eng.holographic_data.toFrontierWord R₁) =
        N.normalize (eng.holographic_data.toFrontierWord R₂) ↔
      FrontierWord.Equiv
        (eng.holographic_data.toFrontierWord R₁)
        (eng.holographic_data.toFrontierWord R₂) :=
  holographic_cannf_detects_record_equiv eng.holographic_data N

/-- Engine-level relative CanNF master theorem: equality of any supplied
relation-parameterized normalizer on holographic outputs is exactly the chosen
relation on those outputs. -/
theorem record_rel_iff_relative_cannf_eq (eng : CanonicalReconstructionEngine setup)
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (N : FrontierWordRelativeNormalizer setup Rel)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    N.normalize (eng.holographic_data.toFrontierWord R₁) =
        N.normalize (eng.holographic_data.toFrontierWord R₂) ↔
      Rel
        (eng.holographic_data.toFrontierWord R₁)
        (eng.holographic_data.toFrontierWord R₂) :=
  holographic_relative_cannf_detects_relation eng.holographic_data N

/-- Engine-level relative CanNF soundness on completed records: once plain
frontier-word equivalence is known to imply the chosen relation, the engine's
holographic output is already invariant under record admin equivalence. -/
theorem record_relative_cannf_eq_of_record_equiv
    (eng : CanonicalReconstructionEngine setup)
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (N : FrontierWordRelativeNormalizer setup Rel)
    (hRel_of_frontier_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → Rel w₁ w₂)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    N.normalize (eng.holographic_data.toFrontierWord R₁) =
      N.normalize (eng.holographic_data.toFrontierWord R₂) :=
  holographic_relative_cannf_sound_on_records
    eng.holographic_data N hRel_of_frontier_equiv h

/-- Engine-level relative CanNF soundness on canonical frontier words: once
plain frontier-word equivalence implies the chosen relation, contextual admin
equivalence of peel chains already forces equality of relative normal forms. -/
theorem canonical_word_relative_cannf_eq_under_admin_equiv
    (eng : CanonicalReconstructionEngine setup)
    {Rel : FrontierWord setup → FrontierWord setup → Prop}
    (N : FrontierWordRelativeNormalizer setup Rel)
    (hRel_of_frontier_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → Rel w₁ w₂)
    {d : Nat}
    {R : CompletedReconstructionRecord setup}
    {c₁ c₂ : PeelChain R}
    (h : PeelChain.ContextualAdminEquiv d c₁ c₂) :
    N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₁ d)) =
      N.normalize (canonicalFrontierWord (FrontierObservation.ofChain c₂ d)) :=
  contextual_admin_equiv_holographic_relative_cannf_eq
    N hRel_of_frontier_equiv h

end CanonicalReconstructionEngine

/-
TEX ref: our_paper_draft.tex, label thm:canonical-reconstruction-algorithm (L1149/L1180)
Paper role: canonical reconstruction algorithm; 3-case descent (tensor/base/sink-peel);
  main completeness theorem for LayerB reconstruction development
Lean status: OVERCLAIM → M0 quarantined; content reclassified as SUPPORT
-/
/- **Quarantine marker (M0)**: support-only boundary for
`thm:canonical-reconstruction-algorithm`.

`CanonicalReconstructionEngine` and its constructors (`ofCurrentDevelopment`,
`ofClosedCanNF`, `ofComputationalCanNF`) provide **SUPPORT infrastructure**
for `thm:canonical-reconstruction-algorithm` (`our_paper_draft.tex` L1149/L1180)
but do NOT constitute a closure of the full manuscript theorem.

**What is supported (proved fields A–G):**
- (A1/A2) Canonical sink existence and key-position maximality.
- (B) Iterated peel descent with chain-length counting.
- (C1–C3) Peel chain existence and canonicality.
- (D) Administrative invariance of frontier words.
- (E1/E2) Replay correctness and stability.
- (F) Holographic bridge data.
- (G1/G2) CanNF detection and sound direction.

**What remains as contract obligations or MISSING declarations:**
- Field (H) `canNF_normalizer` requires `FrontierWordCompleteNormalizer.complete`
  (external contract). `ofClosedCanNF` closes it semantically via a quotient
  existence argument, NOT via an executable canonical normal form algorithm.
- `prop:reconstruction-existence` (MISSING): full algorithm existence.
- `prop:reconstruction-uniqueness` (MISSING): uniqueness up to trace equivalence.
- `prop:reconstruction-termination` (MISSING): termination via well-founded peel-depth.
- `thm:tensor-factor-independence` (MISSING): independence of tensor-factor order.

Downstream spine assemblers must treat `ofClosedCanNF` as a **partial development
package**, not as evidence of full manuscript theorem closure. -/
end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc
-/
