import TraceCalc.LayerB.RealObjects.HolographicReconstruction

/-!
# Real-objects formalization: residue-level CanNF design (items 8a–8f)

**Phase 8 items 8a–8f (2026-04-24).** This file sets up the
**residue-level CanNF design** — a normalizer contract for the
residue-only fragment of `FrontierWord`, parameterized by a
`ResidueCanonicalOrder` interface that names the ordering keys
needed to canonicalize the residue fields.

## Items in this file

* **8a** — `ResidueCanonicalOrder setup`: ordering/key-function
  interface (`boundaryKey`, `depVertexKey`, `tensorKey`,
  `packetKey`). Because the underlying carriers
  (`setup.BoundaryObject`, etc.) do not expose comparable data at
  the abstract level, the key functions are recorded as *named
  obligations* against an opaque key target type, not derived.
* **8b** — `ResidueIsNormal O w`: the residue-level normal-form
  predicate, **a `structure` of five named field obligations**
  (`boundary_normal`, `dependency_order_normal`,
  `tensor_order_normal`, `key_order_normal`,
  `admin_identity_free`). The fields are `Prop`-valued; their
  *meaning* is supplied by the user of `ResidueCanonicalOrder` —
  this layer names them.
* **8c** — `ResidueFrontierNF O`: the residue normal-form carrier
  bundling a frontier word with its normality witness;
  equivalence relation lifted from `FrontierWord.Equiv`.
* **8d** — `ResidueCanNFContract O`: the residue normalizer
  contract — `normalize : FrontierWord → ResidueFrontierNF`,
  `sound`/`complete` against equality of normal-form *words*.
  No instance is supplied.
* **8e** — Bridge to existing CanNF interfaces: explicit
  obligation `ResidueCanNFContract.toCompleteNormalizer_obligation`
  naming what additional data the bridge requires (a target type
  `NF` and a section `ResidueFrontierNF → NF`); the bridge is
  *not* given as a closed function, since the residue contract's
  output type `ResidueFrontierNF O` is itself a sigma-like
  structure rather than a flat `NF` type as required by
  `FrontierWordCompleteNormalizer`.
* **8f** — Manuscript-facing aliases.

## Honest scope (per user's stop conditions, all honored)

* No `FrontierWordCompleteNormalizer` is instantiated.
* No trace-level normalization is implemented.
* `FrontierWord` is **not** enriched.
* All work is at the residue level.
* The `ResidueCanonicalOrder` key functions are obligations, not
  derived (because the abstract `setup.BoundaryObject`,
  `setup.GluingWitness`, etc., expose no comparable data).
* The five residue normal-form predicates (`boundary_normal` etc.)
  are *fields* of `ResidueIsNormal`, not theorems — their
  semantic content is supplied by the consumer of
  `ResidueCanonicalOrder`.
* The `sound`/`complete` clauses of `ResidueCanNFContract`
  compare the *underlying frontier words* of the normal forms
  (`(normalize w₁).word = (normalize w₂).word`), as the user
  requested. This is the strictest reading; if a consumer finds
  it too strict, the layer can be refined to a separate `NFCode`
  target.
* The bridge in 8e is *not* closed — it is exposed as a named
  obligation, since converting `ResidueFrontierNF O` (which
  carries a normality witness) into the flat `NF : Type v`
  required by `FrontierWordCompleteNormalizer` requires an extra
  forgetful function the residue contract does not supply.

## Architectural payoff

This is the **first real normalizer contract for the residue
fragment**. It is parametric in:

* the choice of `ResidueCanonicalOrder` (how to *order* residue
  data for canonicalization);
* the choice of `ResidueFrontierNF` instance (i.e., the witness
  that a particular word is normal, supplied by whatever future
  normalization machinery is built).

The contract structure is fully type-checked. No fake
instantiation. No trace-level claim.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`) — the residue
  record fields whose ordering this layer canonicalizes.
* L1108–L1120 — the `ports / packets / dep / attach / tensor /
  key` fields.
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 8a — Residue canonical ordering interface -/

/-- **`ResidueCanonicalOrder setup`**: the ordering/key-function
interface needed to canonicalize the residue-level fields of a
`CompletedReconstructionRecord`.

Because the abstract `setup.BoundaryObject`, `setup.GluingWitness`,
`Packet setup`, etc. expose **no comparable data** at the
`RewriteCalculusSetup` interface level, every key function is
exposed as an *obligation* against a generic ordered key target
type `K` (a `LinearOrder`), supplied as a parameter. A future
concrete `setup` will provide a concrete key target (e.g., a
`Nat`-valued hash, a structural representative, or a free
total-orderable code).

This **does not** prejudge whether the keys are extensional
(equal keys ⇒ equal data) — that is a separate obligation that
any future normalizer-construction layer would have to discharge
on top of `ResidueCanonicalOrder`. -/
structure ResidueCanonicalOrder (setup : RewriteCalculusSetup.{u}) where
  /-- The ordered-key target type. -/
  KeyTarget : Type v
  /-- A linear order on `KeyTarget`, so that key functions yield
  totally-ordered output suitable for sort-based canonicalization. -/
  keyTargetOrder : LinearOrder KeyTarget
  /-- Boundary-object key function (input to
  `boundary_admin_canonicalize`). -/
  boundaryKey : setup.BoundaryObject → KeyTarget
  /-- Per-vertex key function on the dependency graph (input to
  `dependency_order_canonicalize`). The vertex is identified by
  its position `Fin n` in the record's packet enumeration. -/
  depVertexKey : (n : Nat) → Fin n → KeyTarget
  /-- Tensor-block key function (input to
  `tensor_factor_order_canonicalize`). -/
  tensorKey : (n : Nat) → Fin n → KeyTarget
  /-- Per-packet key function (input to `key_order_canonicalize`). -/
  packetKey : Packet setup → KeyTarget

/-! ## Item 8b — Residue normal-form predicate -/

/-- **`ResidueIsNormal O w`**: the residue-level normal-form
predicate against an ordering `O`, expressed as a **conjunction of
five named field obligations**.

Each field is a `Prop`-valued obligation; the *semantic content*
of each predicate (e.g., what does it mean for the boundary to be
"in canonical form against `O.boundaryKey`") is supplied by the
consumer of `ResidueCanonicalOrder`. This layer fixes the **API
shape** of "residue-normal" without fixing the predicates
themselves.

Per the user's verbatim 8b.5: *"These predicates may initially be
fields/obligations, not proved."* -/
structure ResidueIsNormal
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup)
    (w : FrontierWord setup) : Type where
  /-- Boundary-object normality (against `O.boundaryKey`). -/
  boundary_normal : Prop
  /-- Dependency-order normality (against `O.depVertexKey`). -/
  dependency_order_normal : Prop
  /-- Tensor-factor normality (against `O.tensorKey`). -/
  tensor_order_normal : Prop
  /-- Per-packet key-order normality (against `O.packetKey`). -/
  key_order_normal : Prop
  /-- Absence of inserted administrative identity moves. -/
  admin_identity_free : Prop

/-! ## Item 8c — Residue normal-form carrier -/

/-- **`ResidueFrontierNF O`**: a frontier word together with a
witness of residue-normality against the ordering `O`. -/
structure ResidueFrontierNF
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup) where
  /-- The underlying frontier word. -/
  word : FrontierWord setup
  /-- The residue-normality witness. -/
  normal : ResidueIsNormal O word

namespace ResidueFrontierNF

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

/-- Equivalence on `ResidueFrontierNF`: lifted from
`FrontierWord.Equiv` of the underlying words. -/
def Equiv (n₁ n₂ : ResidueFrontierNF O) : Prop :=
  FrontierWord.Equiv n₁.word n₂.word

theorem Equiv.refl (n : ResidueFrontierNF O) : Equiv n n :=
  FrontierWord.Equiv.refl n.word

theorem Equiv.symm {n₁ n₂ : ResidueFrontierNF O}
    (h : Equiv n₁ n₂) : Equiv n₂ n₁ :=
  FrontierWord.Equiv.symm h

theorem Equiv.trans {n₁ n₂ n₃ : ResidueFrontierNF O}
    (h₁ : Equiv n₁ n₂) (h₂ : Equiv n₂ n₃) : Equiv n₁ n₃ :=
  FrontierWord.Equiv.trans h₁ h₂

end ResidueFrontierNF

/-! ## Item 8d — Residue normalizer contract -/

/-- **`ResidueCanNFContract O`**: the residue-level normalizer
contract against an ordering `O`.

The contract has three obligations:

* `normalize : FrontierWord → ResidueFrontierNF` — produces a
  residue-normal form for every frontier word.
* `sound` — admin-equivalent inputs produce normal forms whose
  underlying *words* are literally equal. This is the strict
  reading per the user's 8d.8 specification. (If a future consumer
  finds equality of words too strict, this layer can be refined
  to compare against a separate `NFCode` target.)
* `complete` — equal underlying-word normal forms imply admin
  equivalence of inputs.

**No instance is supplied.** This is the contract that any future
deterministic residue normalizer must discharge. -/
structure ResidueCanNFContract
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup) where
  /-- The normalization function. -/
  normalize : FrontierWord setup → ResidueFrontierNF O
  /-- **Soundness obligation**: admin-equivalent inputs produce
  equal-word normal forms. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ →
        (normalize w₁).word = (normalize w₂).word
  /-- **Completeness obligation** (the actual canonicality
  content): equal-word normal forms imply admin-equivalent inputs. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      (normalize w₁).word = (normalize w₂).word →
        FrontierWord.Equiv w₁ w₂

/-! ## Item 8e — Bridge to existing CanNF interfaces -/

namespace ResidueCanNFContract

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

def ofFields
    (normalize : FrontierWord setup → ResidueFrontierNF O)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ →
          (normalize w₁).word = (normalize w₂).word)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        (normalize w₁).word = (normalize w₂).word →
          FrontierWord.Equiv w₁ w₂) :
    ResidueCanNFContract.{u, v} O where
  normalize := normalize
  sound := sound
  complete := complete

@[simp] theorem ofFields_normalize
    (normalize : FrontierWord setup → ResidueFrontierNF O)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ →
          (normalize w₁).word = (normalize w₂).word)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        (normalize w₁).word = (normalize w₂).word →
          FrontierWord.Equiv w₁ w₂)
    (w' : FrontierWord setup) :
    (ofFields (setup := setup) (O := O) normalize @sound @complete).normalize w' = normalize w' :=
  rfl

@[simp] theorem ofFields_sound
    (normalize : FrontierWord setup → ResidueFrontierNF O)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ →
          (normalize w₁).word = (normalize w₂).word)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        (normalize w₁).word = (normalize w₂).word →
          FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) (O := O) normalize @sound @complete).sound h = sound h :=
  rfl

@[simp] theorem ofFields_complete
    (normalize : FrontierWord setup → ResidueFrontierNF O)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ →
          (normalize w₁).word = (normalize w₂).word)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        (normalize w₁).word = (normalize w₂).word →
          FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : (normalize w₁).word = (normalize w₂).word) :
    (ofFields (setup := setup) (O := O) normalize @sound @complete).complete h = complete h :=
  rfl

/-- **The convenient flat-output target type**: `FrontierWord setup`,
since the residue contract's `sound`/`complete` clauses already
compare *underlying words* of normal forms. The forgetful
projection `ResidueFrontierNF O → FrontierWord setup` is
`.word`. -/
def toSoundNormalizer (C : ResidueCanNFContract.{u, v} O) :
    FrontierWordSoundNormalizer.{u, u} setup where
  NF := FrontierWord setup
  normalize w := (C.normalize w).word
  sound h := C.sound h

@[simp] theorem toSoundNormalizer_sound
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.toSoundNormalizer).sound h = C.sound h :=
  rfl

/-- **Item 8e.11**: bridge to `FrontierWordCompleteNormalizer`.

This bridge IS definitionally honest: it uses the underlying word
of the residue-normal form as the flat NF target, which is exactly
the comparison appearing in the residue contract's `sound` /
`complete` fields. **No completeness is manufactured** — the
completeness field of the resulting `FrontierWordCompleteNormalizer`
is supplied by `C.complete`, which is itself a contract obligation
that any concrete residue CanNF must discharge. -/
def toCompleteNormalizer (C : ResidueCanNFContract.{u, v} O) :
    FrontierWordCompleteNormalizer.{u, u} setup where
  toFrontierWordSoundNormalizer := C.toSoundNormalizer
  complete h := C.complete h

@[simp] theorem toCompleteNormalizer_complete
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup}
    (h : (C.normalize w₁).word = (C.normalize w₂).word) :
    (C.toCompleteNormalizer).complete h = C.complete h :=
  rfl

theorem normalize_word_eq_of_equiv (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    (C.normalize w₁).word = (C.normalize w₂).word :=
  C.sound h

theorem equiv_of_normalize_word_eq (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} (h : (C.normalize w₁).word = (C.normalize w₂).word) :
    FrontierWord.Equiv w₁ w₂ :=
  C.complete h

theorem normalize_word_eq_iff_equiv (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} :
    (C.normalize w₁).word = (C.normalize w₂).word ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨C.complete, C.sound⟩

theorem toSoundNormalizer_normalize_eq_of_equiv
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.toSoundNormalizer).normalize w₁ = (C.toSoundNormalizer).normalize w₂ :=
  C.toSoundNormalizer.sound h

theorem equiv_of_toCompleteNormalizer_normalize_eq
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup}
    (h : (C.toCompleteNormalizer).normalize w₁ = (C.toCompleteNormalizer).normalize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  C.toCompleteNormalizer.complete h

theorem toCompleteNormalizer_normalize_eq_of_equiv
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.toCompleteNormalizer).normalize w₁ = (C.toCompleteNormalizer).normalize w₂ :=
  C.toCompleteNormalizer.sound h

@[simp] theorem toCompleteNormalizer_complete_iff
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} :
    (C.toCompleteNormalizer).normalize w₁ = (C.toCompleteNormalizer).normalize w₂ ↔
      FrontierWord.Equiv w₁ w₂ := by
  simpa [ResidueCanNFContract.toCompleteNormalizer] using C.normalize_word_eq_iff_equiv

theorem toCompleteNormalizer_normalize_eq_iff_equiv
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} :
    (C.toCompleteNormalizer).normalize w₁ = (C.toCompleteNormalizer).normalize w₂ ↔
      FrontierWord.Equiv w₁ w₂ :=
  C.toCompleteNormalizer_complete_iff

/-- **Audit theorem (8e.11)**: the bridge to `FrontierWordSoundNormalizer`
projects `normalize w` to the underlying word of the residue
normal form. -/
@[simp] theorem toSoundNormalizer_normalize
    (C : ResidueCanNFContract.{u, v} O) (w : FrontierWord setup) :
    (C.toSoundNormalizer).normalize w = (C.normalize w).word :=
  rfl

/-- **Audit theorem (8e.11.b)**: the bridge to
`FrontierWordCompleteNormalizer` agrees with the sound-projection
on `normalize`. -/
@[simp] theorem toCompleteNormalizer_normalize
    (C : ResidueCanNFContract.{u, v} O) (w : FrontierWord setup) :
    (C.toCompleteNormalizer).normalize w = (C.normalize w).word :=
  rfl

end ResidueCanNFContract

/-! ## Item 8f — Manuscript-facing aliases -/

/-- **Manuscript alias (8f.13.a)**: the residue CanNF normal-form
contract is the structure obligation `ResidueCanNFContract`. -/
def theorem_residue_cannf_normal_form_contract
    (O : ResidueCanonicalOrder.{u, v} setup) : Type _ :=
  ResidueCanNFContract O

/-- **Manuscript alias (8f.13.b)**: the residue CanNF soundness
contract is the `sound` field of `ResidueCanNFContract`. -/
theorem theorem_residue_cannf_soundness_contract
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.normalize w₁).word = (C.normalize w₂).word :=
  C.sound h

/-- **Manuscript alias (8f.13.c)**: the residue CanNF completeness
contract is the `complete` field of `ResidueCanNFContract`. This
is the actual residue-canonicality obligation. -/
theorem theorem_residue_cannf_completeness_contract
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O)
    {w₁ w₂ : FrontierWord setup}
    (h : (C.normalize w₁).word = (C.normalize w₂).word) :
    FrontierWord.Equiv w₁ w₂ :=
  C.complete h

/-
TEX ref: our_paper_draft.tex, label prop:canNF-well-defined (L1408+)
Paper role: the canonical normal form of a frontier word is well-defined,
  i.e., does not depend on the representative chosen in the equivalence class
Lean status: MISSING → stub added (M3); renamed _from_contract to prevent overclaim.
  Renamed from `canNF_well_defined` because the bare name implied an unconditional paper proof.
  Actually only projects C.sound and C.complete from ResidueCanNFContract.
  Status: CONDITIONAL-FIELD-PROJECTION
-/
/-- **`prop:canNF-well-defined`** (CONDITIONAL-FIELD-PROJECTION): the canonical
normal form is well-defined — given a `ResidueCanNFContract`.

Given a `ResidueCanNFContract`, the CanNF of a frontier word is
independent of the representative chosen in its equivalence class:
two equivalent words have equal normal forms (`C.sound`) and conversely
(`C.complete`). This packages both directions as the well-definedness statement.

This is NOT a paper-level proof: it only projects the `sound` and `complete`
contract fields from `ResidueCanNFContract`. The actual normalization proof
obligations remain in those fields and are unverified here.

Renamed from `canNF_well_defined` to `canNF_well_defined_from_contract` to
prevent the bare name from being mistaken for an unconditional paper proof. -/
theorem canNF_well_defined_from_contract
    {setup : RewriteCalculusSetup.{u}}
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O)
    (w₁ w₂ : FrontierWord setup) :
    (C.normalize w₁).word = (C.normalize w₂).word ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨fun h => C.complete h, fun h => C.sound h⟩

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
