import TraceCalc.LayerB.RealObjects.ResidueCanNF

/-!
# Real-objects formalization: residue NF-code contract and key-stability (items 8g–8k)

**Phase 8 items 8g–8k (2026-04-24).** Pressure-test layer for the
residue-level CanNF: introduces `ResidueNFCodeContract` (a CanNF
contract that targets a free *NF code type* rather than a normalized
`FrontierWord`), bridges from `ResidueCanNFContract` (item 8d), gives
the holographic detection theorem in NF-code form, and names the
*key-stability obligations* that any concrete `ResidueCanonicalOrder`
must discharge to be invariant under `BoundaryAdminEquiv`.

The motivation is the user's verbatim 8g–8k directive: equality of
normalized `FrontierWord` values (the strict reading of item 8d) may
later prove too strict for some concrete normalizers, whereas equality
of *abstract NF codes* — opaque values produced by `code` — gives
exactly the right freedom (`code(w₁) = code(w₂) ⇔ w₁ ∼₍∂admin₎ w₂`).

## Items in this file

* **8g** — `ResidueNFCodeSoundContract` / `ResidueNFCodeContract`:
  the *NF-code* CanNF contract — `NFCode : Type w`,
  `code : FrontierWord → NFCode`, `sound`/`complete` against equality
  of codes. Split sound-only / sound+complete in parallel with
  `FrontierWordSoundNormalizer` / `FrontierWordCompleteNormalizer`.
* **8h** — `ResidueCanNFContract.toResidueNFCodeContract`: bridge
  from the word-equality contract (item 8d) to the NF-code contract
  by taking `NFCode := FrontierWord setup` and
  `code w := (C.normalize w).word`. Definitionally honest — no
  completeness manufactured.
* **8i** — `holographic_residue_nfcode_detects_record_equiv`: the
  holographic detection theorem in NF-code form, parametric in any
  `ResidueNFCodeContract`. Both directions are appeals to the
  contract obligations.
* **8j** — `ResidueKeyStabilityObligations`: names the four
  key-stability obligations any concrete `ResidueCanonicalOrder`
  must discharge to be admin-invariant. The boundary-key obligation
  has a real signature (`BoundaryAdminEquiv`-stability of
  `O.boundaryKey`); the other three keys have no admin-equivalence
  relation defined at this abstract level, so they are exposed as
  named `Prop` obligations to be filled in once their corresponding
  admin-equivalences exist.
* **8k** — Manuscript-facing aliases.

## Honest scope (per user's stop conditions, all honored)

* No concrete `ResidueCanonicalOrder` instance is supplied.
* No concrete `ResidueNFCodeContract` instance is supplied.
* No concrete `ResidueCanNFContract` instance is supplied.
* `FrontierWord` is **not** enriched.
* No trace-level normalization is implemented.
* Three of the four key-stability obligations remain abstract `Prop`
  obligations (no admin-permutation machinery exists for `Fin n`
  vertices, tensor positions, or packets at this layer).

## Architectural payoff

`ResidueNFCodeContract` is *strictly weaker* than
`ResidueCanNFContract` in the sense that **every word-equality
contract is also an NF-code contract** (via the 8h bridge), but the
NF-code contract permits a future normalizer whose canonical output
is a hash, an opaque code, or a sorted/multiset representative
**without** committing to a normalized `FrontierWord` value. This
gives the implementation freedom to build canonical codes stable
under `BoundaryAdminEquiv` first and only lift to a normalized word
once that ordering exists.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`).
* L1108–L1120 — the `ports / packets / dep / attach / tensor / key`
  fields.
-/

universe u v w

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Concrete quotient-coded NF target -/

namespace FrontierWord

/-- Setoid on frontier words induced by `FrontierWord.Equiv`. This is the
honest quotient carrier behind the first concrete NF-code contract: we record
admin-equivalence classes directly, without pretending to have built a stricter
residue normalizer. -/
def equivSetoid (setup : RewriteCalculusSetup.{u}) : Setoid (FrontierWord setup) where
  r := Equiv
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact Equiv.refl w
    · intro w₁ w₂ h
      exact Equiv.symm h
    · intro w₁ w₂ w₃ h₁ h₂
      exact Equiv.trans h₁ h₂

/-- Concrete quotient carrier of frontier words modulo boundary-admin
equivalence. This is tautological but honest: equality in the quotient is
exactly the completeness target of `ResidueNFCodeContract`. -/
def EquivClass (setup : RewriteCalculusSetup.{u}) : Type u :=
  Quotient (equivSetoid setup)

/-- Constructor for the admin-equivalence class of a frontier word. -/
def EquivClass.mk {setup : RewriteCalculusSetup.{u}}
    (w : FrontierWord setup) : EquivClass setup :=
  Quotient.mk (equivSetoid setup) w

end FrontierWord

/-! ## Item 8g — Residue NF-code contract -/

/-- **`ResidueNFCodeSoundContract O`** (item 8g, sound-only half):
the residue NF-code contract carrying the *cheap half* — every
admin-equivalent pair of frontier words has equal NF codes.

Mirrors `FrontierWordSoundNormalizer` (item 5r) but parameterized
over an ordering `O : ResidueCanonicalOrder`. -/
structure ResidueNFCodeSoundContract
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup) where
  /-- The NF-code target type. Opaque — may be a sorted
  list, a multiset representative, a hash, etc. -/
  NFCode : Type w
  /-- The NF-code function. -/
  code : FrontierWord setup → NFCode
  /-- **Soundness obligation**: admin-equivalent inputs produce
  equal NF codes. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂

namespace ResidueNFCodeSoundContract

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

def ofFields
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂) :
    ResidueNFCodeSoundContract.{u, v, w} O where
  NFCode := NFCode
  code := code
  sound := sound

@[simp] theorem ofFields_NFCode
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂) :
    (ofFields (setup := setup) (O := O) NFCode code @sound).NFCode = NFCode :=
  rfl

@[simp] theorem ofFields_code
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (w' : FrontierWord setup) :
    (ofFields (setup := setup) (O := O) NFCode code @sound).code w' = code w' :=
  rfl

@[simp] theorem ofFields_sound
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) (O := O) NFCode code @sound).sound h = sound h :=
  rfl

theorem code_eq_of_equiv (C : ResidueNFCodeSoundContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    C.code w₁ = C.code w₂ :=
  C.sound h

end ResidueNFCodeSoundContract

/-- **`ResidueNFCodeContract O`** (item 8g, full contract): adds
the canonicality (completeness) obligation. Mirrors
`FrontierWordCompleteNormalizer` (item 5r). -/
structure ResidueNFCodeContract
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup)
    extends ResidueNFCodeSoundContract.{u, v, w} O where
  /-- **Completeness obligation** (the actual residue canonicality
  content): equal NF codes imply admin-equivalent inputs. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂

/-! ### Bridges from NF-code contracts to flat normalizer interfaces -/

namespace ResidueNFCodeSoundContract

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

/-- **NF-code → flat sound normalizer**: an NF-code sound contract
projects directly to a `FrontierWordSoundNormalizer` by taking the
NF-code as the flat NF target. -/
def toFrontierWordSoundNormalizer
    (C : ResidueNFCodeSoundContract.{u, v, w} O) :
    FrontierWordSoundNormalizer.{u, w} setup where
  NF := C.NFCode
  normalize w := C.code w
  sound h := C.sound h

@[simp] theorem toFrontierWordSoundNormalizer_normalize
    (C : ResidueNFCodeSoundContract.{u, v, w} O)
    (w' : FrontierWord setup) :
    C.toFrontierWordSoundNormalizer.normalize w' = C.code w' :=
  rfl

@[simp] theorem toFrontierWordSoundNormalizer_sound
    (C : ResidueNFCodeSoundContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    C.toFrontierWordSoundNormalizer.sound h = C.sound h :=
  rfl

end ResidueNFCodeSoundContract

namespace ResidueNFCodeContract

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

/-- **NF-code → flat complete normalizer**: an NF-code contract
projects directly to a `FrontierWordCompleteNormalizer` — both
directions of the contract are supplied by the contract's own
obligations. **No completeness manufactured.** -/
def toFrontierWordCompleteNormalizer
    (C : ResidueNFCodeContract.{u, v, w} O) :
    FrontierWordCompleteNormalizer.{u, w} setup where
  toFrontierWordSoundNormalizer :=
    ResidueNFCodeSoundContract.toFrontierWordSoundNormalizer
      (ResidueNFCodeContract.toResidueNFCodeSoundContract C)
  complete h := C.complete h

/-- First honest concrete residue NF-code contract.

This is quotient-coded rather than residue-normalizing: it sends a frontier word
to its `FrontierWord.Equiv` class. Soundness is `Quotient.sound`, and
completeness is the fact that equal quotient classes identify equivalent input
words. No fake residue normality witness is introduced. -/
def frontierWordEquivResidueNFCodeContract
    (O : ResidueCanonicalOrder.{u, v} setup) :
    ResidueNFCodeContract.{u, v, u} O where
  NFCode := FrontierWord.EquivClass setup
  code w := FrontierWord.EquivClass.mk w
  sound h := Quotient.sound h
  complete h := Quotient.exact h

def ofFields
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂) :
    ResidueNFCodeContract.{u, v, w} O where
  toResidueNFCodeSoundContract :=
    ResidueNFCodeSoundContract.ofFields (setup := setup) (O := O) NFCode code @sound
  complete := complete

@[simp] theorem ofFields_NFCode
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) (O := O) NFCode code @sound @complete).NFCode = NFCode :=
  rfl

@[simp] theorem ofFields_code
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂)
    (w' : FrontierWord setup) :
    (ofFields (setup := setup) (O := O) NFCode code @sound @complete).code w' = code w' :=
  rfl

@[simp] theorem ofFields_sound
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) (O := O) NFCode code @sound @complete).sound h = sound h :=
  rfl

@[simp] theorem ofFields_complete
    (NFCode : Type w)
    (code : FrontierWord setup → NFCode)
    (sound :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → code w₁ = code w₂)
    (complete :
      ∀ {w₁ w₂ : FrontierWord setup},
        code w₁ = code w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : code w₁ = code w₂) :
    (ofFields (setup := setup) (O := O) NFCode code @sound @complete).complete h = complete h :=
  rfl

@[simp] theorem frontierWordEquivResidueNFCodeContract_code
    (O : ResidueCanonicalOrder.{u, v} setup) (w : FrontierWord setup) :
    (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w =
      FrontierWord.EquivClass.mk w :=
  rfl

theorem code_eq_of_equiv (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    C.code w₁ = C.code w₂ :=
  C.sound h

theorem equiv_of_code_eq (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} (h : C.code w₁ = C.code w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  C.complete h

theorem code_eq_iff_equiv (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} :
    C.code w₁ = C.code w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨C.complete, C.sound⟩

@[simp] theorem toFrontierWordCompleteNormalizer_normalize
    (C : ResidueNFCodeContract.{u, v, w} O)
    (w' : FrontierWord setup) :
    C.toFrontierWordCompleteNormalizer.normalize w' = C.code w' :=
  rfl

@[simp] theorem toFrontierWordCompleteNormalizer_complete
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : C.code w₁ = C.code w₂) :
    C.toFrontierWordCompleteNormalizer.complete h = C.complete h :=
  rfl

theorem toFrontierWordCompleteNormalizer_normalize_eq_iff_equiv
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} :
    C.toFrontierWordCompleteNormalizer.normalize w₁ =
      C.toFrontierWordCompleteNormalizer.normalize w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  C.code_eq_iff_equiv

theorem frontierWordEquivResidueNFCodeContract_code_eq_of_equiv
    (O : ResidueCanonicalOrder.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₁ =
      (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₂ :=
  Quotient.sound h

theorem frontierWordEquivResidueNFCodeContract_equiv_of_code_eq
    (O : ResidueCanonicalOrder.{u, v} setup)
    {w₁ w₂ : FrontierWord setup}
    (h : (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₁ =
      (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  Quotient.exact h

theorem frontierWordEquivResidueNFCodeContract_code_eq_iff_equiv
    (O : ResidueCanonicalOrder.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} :
    (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₁ =
      (frontierWordEquivResidueNFCodeContract (setup := setup) O).code w₂ ↔
        FrontierWord.Equiv w₁ w₂ :=
  ⟨frontierWordEquivResidueNFCodeContract_equiv_of_code_eq (setup := setup) O,
    frontierWordEquivResidueNFCodeContract_code_eq_of_equiv (setup := setup) O⟩

end ResidueNFCodeContract

/-! ## Item 8h — Bridge from the word-equality contract -/

namespace ResidueCanNFContract

variable {setup : RewriteCalculusSetup.{u}}
  {O : ResidueCanonicalOrder.{u, v} setup}

/-- **`ResidueCanNFContract.toResidueNFCodeContract`** (item 8h):
every word-equality residue contract (item 8d) is in particular an
NF-code contract, by taking `NFCode := FrontierWord setup` and
`code w := (C.normalize w).word`.

The contract obligations transport directly: `sound`/`complete` of
the NF-code contract are *literally* `sound`/`complete` of the
word-equality contract. **No content is manufactured.** -/
def toResidueNFCodeContract (C : ResidueCanNFContract.{u, v} O) :
    ResidueNFCodeContract.{u, v, u} O where
  NFCode := FrontierWord setup
  code w := (C.normalize w).word
  sound h := C.sound h
  complete h := C.complete h

/-- **Audit theorem (8h.b)**: the NF-code bridge agrees with the
sound-projection on `code`. -/
@[simp] theorem toResidueNFCodeContract_code
    (C : ResidueCanNFContract.{u, v} O) (w : FrontierWord setup) :
  (ResidueCanNFContract.toResidueNFCodeContract C).code w = (C.normalize w).word :=
  rfl

theorem toResidueNFCodeContract_code_eq_iff_equiv
    (C : ResidueCanNFContract.{u, v} O)
    {w₁ w₂ : FrontierWord setup} :
    (ResidueCanNFContract.toResidueNFCodeContract C).code w₁ =
      (ResidueCanNFContract.toResidueNFCodeContract C).code w₂ ↔
      FrontierWord.Equiv w₁ w₂ :=
  ResidueNFCodeContract.code_eq_iff_equiv (ResidueCanNFContract.toResidueNFCodeContract C)

end ResidueCanNFContract

/-! ## Item 8i — Holographic detection theorem in NF-code form -/

/-- **Holographic NF-code detection theorem (item 8i, complete
direction)**: against any `ResidueNFCodeContract C` and any
`HolographicReconstructionData D`, equality of NF-code images is
iff frontier-word equivalence.

Both directions appeal to the contract: the forward direction is
`C.complete`, the backward direction is `C.sound`. **No CanNF is
constructed here** — the contract is a hypothesis. -/
theorem holographic_residue_nfcode_detects_record_equiv
    {O : ResidueCanonicalOrder.{u, v} setup}
    (D : HolographicReconstructionData setup)
    (C : ResidueNFCodeContract.{u, v, w} O)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    C.code (D.toFrontierWord R₁) = C.code (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  ⟨C.complete, C.sound⟩

/-- **Holographic NF-code sound-direction theorem (item 8i.b)**:
needs only the *sound* half of the NF-code contract — no
completeness assumed. Routes through `D.sound_on_records` (item 7a)
+ `C.sound`. -/
theorem holographic_residue_nfcode_sound_on_records
    {O : ResidueCanonicalOrder.{u, v} setup}
    (D : HolographicReconstructionData setup)
    (C : ResidueNFCodeSoundContract.{u, v, w} O)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    C.code (D.toFrontierWord R₁) = C.code (D.toFrontierWord R₂) :=
  C.sound (D.sound_on_records h)

/-! ## Item 8j — Residue key-stability obligations -/

/-- **`ResidueKeyStabilityObligations O`** (item 8j): names the four
*key-stability* obligations that any concrete `ResidueCanonicalOrder`
must discharge to produce keys invariant under administrative
equivalence.

* `boundary_key_admin_stable` — the boundary key function is
  invariant under `BoundaryAdminEquiv` (the genuine residue admin
  equivalence on boundary objects, item 5e). **This is the only
  field with a fully signed obligation**, since
  `BoundaryAdminEquiv` is the only admin-equivalence relation
  available at the abstract `RewriteCalculusSetup` level.
* `dep_vertex_key_admin_stable`, `tensor_key_admin_stable`,
  `packet_key_admin_stable` — the analogous obligations for the
  per-vertex / tensor-position / packet keys. **No admin-equivalence
  is defined for these carriers at this abstract layer**, so the
  obligations are exposed as named `Prop` placeholders for any
  consumer that brings such admin-permutation machinery to bear.

Per `INV CanNF-Contract`: this is **not** instantiated here; it is
recorded as the contract whose discharge is part of the substantive
future work of building a concrete residue normalizer. -/
structure ResidueKeyStabilityObligations
    {setup : RewriteCalculusSetup.{u}}
    (O : ResidueCanonicalOrder.{u, v} setup) where
  /-- **Boundary key admin-stability**: the boundary key function
  is invariant under `BoundaryAdminEquiv`. The only key-stability
  obligation that has a real signature at this layer. -/
  boundary_key_admin_stable :
    ∀ {Y₁ Y₂ : setup.BoundaryObject},
      BoundaryAdminEquiv Y₁ Y₂ → O.boundaryKey Y₁ = O.boundaryKey Y₂
  /-- **Per-vertex dependency-key admin-stability**: obligation
  placeholder until vertex-permutation admin-equivalence exists. -/
  dep_vertex_key_admin_stable : Prop
  /-- **Tensor-position key admin-stability**: obligation placeholder
  until tensor-position admin-equivalence exists. -/
  tensor_key_admin_stable : Prop
  /-- **Packet key admin-stability**: obligation placeholder until
  packet admin-equivalence exists. -/
  packet_key_admin_stable : Prop

/-! ## Item 8k — Manuscript-facing aliases -/

/-- **Manuscript alias (8k.a)**: the residue NF-code contract is
the obligation `ResidueNFCodeContract`. -/
def theorem_residue_nfcode_contract
    (O : ResidueCanonicalOrder.{u, v} setup) : Type _ :=
  ResidueNFCodeContract.{u, v, w} O

/-- **Manuscript alias (8k.b)**: every word-equality residue
contract is in particular an NF-code contract. -/
def theorem_residue_cannf_refines_nfcode
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueCanNFContract O) :
    ResidueNFCodeContract.{u, v, u} O :=
  C.toResidueNFCodeContract

/-- **Manuscript alias (8k.c)**: the holographic CanNF detection
theorem holds parametrically in any NF-code contract — equality of
NF codes detects admin-equivalence of frontier words. -/
theorem theorem_holographic_residue_nfcode_detects_admin_equiv
    {O : ResidueCanonicalOrder.{u, v} setup}
    (D : HolographicReconstructionData setup)
    (C : ResidueNFCodeContract.{u, v, w} O)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    C.code (D.toFrontierWord R₁) = C.code (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  holographic_residue_nfcode_detects_record_equiv D C

/-- **Manuscript alias (8k.d)**: the four residue canonical keys
admit *named* admin-stability obligations — for the boundary key,
the obligation is the genuine `BoundaryAdminEquiv`-invariance
statement; for the other three keys, the obligations are abstract
`Prop` placeholders pending future admin-permutation machinery. -/
def theorem_residue_canonical_keys_admin_stability_obligations
    (O : ResidueCanonicalOrder.{u, v} setup) : Type _ :=
  ResidueKeyStabilityObligations O

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
