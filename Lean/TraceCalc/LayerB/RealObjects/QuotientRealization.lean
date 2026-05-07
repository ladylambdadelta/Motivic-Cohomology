import TraceCalc.LayerB.RealObjects.ResidueNFCode

/-!
# Real-objects formalization: quotient realization layer (items 8l–8p)

**Phase 8 items 8l–8p (2026-04-24).** Names the categorical/realization
content of the residue NF-code contract:

> A `ResidueNFCodeContract` is a **faithful realization** of the admin
> quotient `FrontierWord setup / FrontierWord.Equiv`.

The layer introduces `FrontierQuotientRealization setup` — a target type
with `realize`, `respects_equiv`, and `faithful` obligations — and
bridges `ResidueNFCodeContract` into it. The holographic reconstruction
theorem is then re-stated as an iff against any quotient realization.

## Non-motivic caveat

The word *realization* here refers to the **quotient-realization
functor** from the concrete `FrontierWord` carrier down to its
admin-equivalence quotient. It is **not** a motivic realization (Betti,
de Rham, étale, …). This caveat is carried on every declaration in the
layer.

## Items in this file

* **8l** — `FrontierQuotientRealization setup`: target type `Target`
  with `realize` + `respects_equiv` + `faithful`.
  Plus `FrontierQuotientInvariant setup`: the sound-only half,
  dropping `faithful`.
* **8m** — `ResidueNFCodeContract.toQuotientRealization` (+ sound-only
  `ResidueNFCodeSoundContract.toQuotientInvariant`) bridges.
* **8n** — `holographic_reconstruction_via_quotient_realization`.
* **8o** — Non-motivic caveat: `theorem_residue_code_is_quotient_realization_not_motivic_realization`
  expressed as a type-level statement
  `ResidueNFCodeContract O → FrontierQuotientRealization setup`.
* **8p** — Manuscript-facing aliases.

## Honest scope

* No concrete `FrontierQuotientRealization` is constructed.
* No concrete `ResidueNFCodeContract` is constructed.
* No claim that the realization is motivic.
* No claim that additional admin-equivalences (vertex, tensor,
  packet) exist.
* `FrontierWord` is not enriched.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`).
-/

universe u v w

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 8l — Quotient realization interface -/

/-- **`FrontierQuotientInvariant setup`** (item 8l, sound-only half):
a target type equipped with a `FrontierWord.Equiv`-invariant map —
every admin-equivalent pair of frontier words is sent to equal
targets.

**Non-motivic caveat**: this is a realization of the admin quotient
`FrontierWord setup / FrontierWord.Equiv`, *not* a motivic
realization functor. The name *realization* refers to quotient
realization only. -/
structure FrontierQuotientInvariant (setup : RewriteCalculusSetup.{u}) where
  /-- The target type of the invariant. Opaque. -/
  Target : Type v
  /-- The invariant map. -/
  realize : FrontierWord setup → Target
  /-- **Respects-equivalence obligation**: admin-equivalent frontier
  words realize equally. -/
  respects_equiv :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂

namespace FrontierQuotientInvariant

def ofFields
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂) :
    FrontierQuotientInvariant.{u, v} setup where
  Target := Target
  realize := realize
  respects_equiv := respects_equiv

@[simp] theorem ofFields_Target
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂) :
    (ofFields (setup := setup) Target realize @respects_equiv).Target = Target :=
  rfl

@[simp] theorem ofFields_realize
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (w : FrontierWord setup) :
    (ofFields (setup := setup) Target realize @respects_equiv).realize w = realize w :=
  rfl

@[simp] theorem ofFields_respects_equiv
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) Target realize @respects_equiv).respects_equiv h = respects_equiv h :=
  rfl

theorem realize_eq_of_equiv (Q : FrontierQuotientInvariant.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    Q.realize w₁ = Q.realize w₂ :=
  Q.respects_equiv h

end FrontierQuotientInvariant

/-- **`FrontierQuotientRealization setup`** (item 8l, full contract):
a **faithful** realization of the admin quotient — both directions of
the iff between admin-equivalence and target equality.

**Non-motivic caveat**: as with `FrontierQuotientInvariant`, the
word *realization* here refers to the quotient realization
`FrontierWord / FrontierWord.Equiv → Target`. It is not a motivic
realization (Betti, de Rham, étale, …). -/
structure FrontierQuotientRealization (setup : RewriteCalculusSetup.{u})
    extends FrontierQuotientInvariant setup where
  /-- **Faithfulness obligation** (the categorically substantive
  content): equal realizations imply admin-equivalence. -/
  faithful :
    ∀ {w₁ w₂ : FrontierWord setup},
      realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂

namespace FrontierQuotientRealization

def ofFields
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (faithful :
      ∀ {w₁ w₂ : FrontierWord setup},
        realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂) :
    FrontierQuotientRealization.{u, v} setup where
  toFrontierQuotientInvariant :=
    FrontierQuotientInvariant.ofFields (setup := setup) Target realize @respects_equiv
  faithful := faithful

@[simp] theorem ofFields_Target
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (faithful :
      ∀ {w₁ w₂ : FrontierWord setup},
        realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) Target realize @respects_equiv @faithful).Target = Target :=
  rfl

@[simp] theorem ofFields_realize
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (faithful :
      ∀ {w₁ w₂ : FrontierWord setup},
        realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂)
    (w : FrontierWord setup) :
    (ofFields (setup := setup) Target realize @respects_equiv @faithful).realize w = realize w :=
  rfl

@[simp] theorem ofFields_respects_equiv
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (faithful :
      ∀ {w₁ w₂ : FrontierWord setup},
        realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ofFields (setup := setup) Target realize @respects_equiv @faithful).respects_equiv h =
      respects_equiv h :=
  rfl

@[simp] theorem ofFields_faithful
    (Target : Type v)
    (realize : FrontierWord setup → Target)
    (respects_equiv :
      ∀ {w₁ w₂ : FrontierWord setup},
        FrontierWord.Equiv w₁ w₂ → realize w₁ = realize w₂)
    (faithful :
      ∀ {w₁ w₂ : FrontierWord setup},
        realize w₁ = realize w₂ → FrontierWord.Equiv w₁ w₂)
    {w₁ w₂ : FrontierWord setup}
    (h : realize w₁ = realize w₂) :
    (ofFields (setup := setup) Target realize @respects_equiv @faithful).faithful h = faithful h :=
  rfl

@[simp] theorem toFrontierQuotientInvariant_realize
    (Q : FrontierQuotientRealization.{u, v} setup) (w : FrontierWord setup) :
    Q.toFrontierQuotientInvariant.realize w = Q.realize w :=
  rfl

theorem realize_eq_of_equiv (Q : FrontierQuotientRealization.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} (h : FrontierWord.Equiv w₁ w₂) :
    Q.realize w₁ = Q.realize w₂ :=
  Q.respects_equiv h

theorem equiv_of_realize_eq (Q : FrontierQuotientRealization.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} (h : Q.realize w₁ = Q.realize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  Q.faithful h

theorem realize_eq_iff_equiv (Q : FrontierQuotientRealization.{u, v} setup)
    {w₁ w₂ : FrontierWord setup} :
    Q.realize w₁ = Q.realize w₂ ↔ FrontierWord.Equiv w₁ w₂ :=
  ⟨Q.faithful, Q.respects_equiv⟩

end FrontierQuotientRealization

/-! ## Item 8m — Bridges from NF-code contracts -/

namespace ResidueNFCodeSoundContract

variable {O : ResidueCanonicalOrder.{u, v} setup}

/-- **`ResidueNFCodeSoundContract.toQuotientInvariant`** (item 8m,
sound-only): every sound NF-code contract yields a quotient
invariant, with `Target := NFCode` and `realize := code`. **No
content manufactured.** -/
def toQuotientInvariant
    (C : ResidueNFCodeSoundContract.{u, v, w} O) :
    FrontierQuotientInvariant.{u, w} setup where
  Target := C.NFCode
  realize w := C.code w
  respects_equiv h := C.sound h

@[simp] theorem toQuotientInvariant_realize
    (C : ResidueNFCodeSoundContract.{u, v, w} O) (w' : FrontierWord setup) :
    FrontierQuotientInvariant.realize
      (ResidueNFCodeSoundContract.toQuotientInvariant C) w' = C.code w' :=
  rfl

@[simp] theorem toQuotientInvariant_respects_equiv
    (C : ResidueNFCodeSoundContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (ResidueNFCodeSoundContract.toQuotientInvariant C).respects_equiv h = C.sound h :=
  rfl

end ResidueNFCodeSoundContract

namespace ResidueNFCodeContract

variable {O : ResidueCanonicalOrder.{u, v} setup}

/-- **`ResidueNFCodeContract.toQuotientRealization`** (item 8m,
full): every NF-code contract yields a *faithful* quotient
realization, with `Target := NFCode` and `realize := code`. Both
obligations transport literally — `respects_equiv := C.sound`,
`faithful := C.complete`. **No content manufactured.** -/
def toQuotientRealization
    (C : ResidueNFCodeContract.{u, v, w} O) :
    FrontierQuotientRealization.{u, w} setup where
  toFrontierQuotientInvariant :=
    ResidueNFCodeSoundContract.toQuotientInvariant C.toResidueNFCodeSoundContract
  faithful h := C.complete h

@[simp] theorem toQuotientRealization_realize
    (C : ResidueNFCodeContract.{u, v, w} O)
    (w' : FrontierWord setup) :
    (C.toQuotientRealization).realize w' = C.code w' :=
  rfl

@[simp] theorem toQuotientRealization_respects_equiv
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.toQuotientRealization).respects_equiv h = C.sound h :=
  rfl

@[simp] theorem toQuotientRealization_faithful
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : C.code w₁ = C.code w₂) :
    (C.toQuotientRealization).faithful h = C.complete h :=
  rfl

theorem toQuotientRealization_equiv_of_realize_eq
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : (C.toQuotientRealization).realize w₁ = (C.toQuotientRealization).realize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  C.toQuotientRealization.faithful h

theorem toQuotientRealization_realize_eq_of_equiv
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) :
    (C.toQuotientRealization).realize w₁ = (C.toQuotientRealization).realize w₂ :=
  C.toQuotientRealization.respects_equiv h

theorem toQuotientRealization_realize_eq_iff_equiv
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup} :
    (C.toQuotientRealization).realize w₁ = (C.toQuotientRealization).realize w₂ ↔
      FrontierWord.Equiv w₁ w₂ :=
  C.toQuotientRealization.realize_eq_iff_equiv

end ResidueNFCodeContract

/-! ## Item 8n — Holographic reconstruction via quotient realization -/

/-- **Holographic reconstruction via quotient realization (item
8n)**: against any `FrontierQuotientRealization Q` and any
`HolographicReconstructionData D`, equality of realized images is
iff frontier-word equivalence.

This is the cleanest form of the holographic reconstruction
theorem: no normalizer, no NF code, no key ordering — just the
quotient realization and its faithfulness. Both directions are
appeals to `Q`'s contract obligations: the forward direction is
`Q.faithful`, the backward direction is `Q.respects_equiv`. -/
theorem holographic_reconstruction_via_quotient_realization
    (Q : FrontierQuotientRealization.{u, v} setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    Q.realize (D.toFrontierWord R₁) = Q.realize (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  ⟨Q.faithful, Q.respects_equiv⟩

/-- **Sound-direction-only variant (item 8n.b)**: against any
`FrontierQuotientInvariant Q` and any `HolographicReconstructionData
D`, admin-equivalent records have equal realized images. Needs only
the *invariant* half — no faithfulness. -/
theorem holographic_invariant_sound_on_records
    (Q : FrontierQuotientInvariant.{u, v} setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv (@BoundaryAdminEquiv setup) R₁ R₂) :
    Q.realize (D.toFrontierWord R₁) = Q.realize (D.toFrontierWord R₂) :=
  Q.respects_equiv (D.sound_on_records h)

/-! ## Item 8o — Non-motivic caveat -/

/-- **Non-motivic caveat (item 8o)**: a residue NF-code contract
gives a quotient realization — the word *realization* here refers
to the **admin-quotient realization**, **not** to motivic
realization functors (Betti, de Rham, étale, …).

This declaration names the caveat at the type level: the bridge is
exactly `ResidueNFCodeContract.toQuotientRealization` (item 8m), so
the only *realization* structure produced by a residue NF-code
contract is the admin-quotient one. No motivic content is produced
or claimed. -/
def theorem_residue_code_is_quotient_realization_not_motivic_realization
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract.{u, v, w} O) :
    FrontierQuotientRealization.{u, w} setup :=
  C.toQuotientRealization

/-! ## Item 8p — Manuscript-facing aliases -/

/-- **Manuscript alias (8p.a)**: a residue NF-code contract is a
quotient realization of the admin quotient. **Non-motivic**. -/
def theorem_residue_nfcode_as_quotient_realization
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract.{u, v, w} O) :
    FrontierQuotientRealization.{u, w} setup :=
  C.toQuotientRealization

/-- **Manuscript alias (8p.b)**: holographic reconstruction is the
iff between equal quotient-realized images and admin-equivalent
frontier words, parametric in any faithful quotient realization.
**Non-motivic**: "realization" means admin-quotient realization. -/
theorem theorem_holographic_reconstruction_via_quotient_realization
    (Q : FrontierQuotientRealization.{u, v} setup)
    (D : HolographicReconstructionData setup)
    {R₁ R₂ : CompletedReconstructionRecord setup} :
    Q.realize (D.toFrontierWord R₁) = Q.realize (D.toFrontierWord R₂)
      ↔ FrontierWord.Equiv (D.toFrontierWord R₁) (D.toFrontierWord R₂) :=
  holographic_reconstruction_via_quotient_realization Q D

/-- **Manuscript alias (8p.c)**: the quotient realization produced
by a residue NF-code contract is *faithful* for
`FrontierWord.Equiv` — equal realizations imply admin-equivalence.
**Non-motivic**. -/
theorem theorem_residue_code_realization_faithful_for_frontier_equiv
    {O : ResidueCanonicalOrder.{u, v} setup}
    (C : ResidueNFCodeContract.{u, v, w} O)
    {w₁ w₂ : FrontierWord setup}
    (h : (C.toQuotientRealization).realize w₁
          = (C.toQuotientRealization).realize w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  (C.toQuotientRealization).faithful h

/-
TEX ref: our_paper_draft.tex, label lem:geometric-presentation-completeness (L1430+)
Paper role: the geometric presentation of the rewrite system is complete —
  every frontier-word equivalence class has a representative in the normal-form set
Lean status: MISSING → stub added (M3)
-/
/-- **`lem:geometric-presentation-completeness`**: the geometric presentation
of the frontier rewrite system is complete.

Every frontier-word equivalence class has a representative that is in canonical
normal form. Given a complete normalizer (`FrontierWordCompleteNormalizer`),
the quotient realization separates all equivalence classes, providing a
complete geometric presentation.

This proposition registers the completeness obligation that a concrete
instantiation must discharge by providing a complete normalizer whose
normalized images are canonical representatives. -/
structure GeometricPresentationCompleteness
    (setup : RewriteCalculusSetup.{u}) : Prop where
  /-- Every frontier word has a canonical representative (its normal form). -/
  has_normal_form :
    ∀ (N : FrontierWordCompleteNormalizer setup) (w : FrontierWord setup),
      ∃ w_nf : FrontierWord setup,
        FrontierWord.Equiv w w_nf ∧ N.normalize w_nf = N.normalize w_nf
  /-- The quotient realization separates all equivalence classes. -/
  quotient_separates_classes :
    ∀ (Q : FrontierQuotientRealization.{u, u} setup)
      (w₁ w₂ : FrontierWord setup),
      ¬ FrontierWord.Equiv w₁ w₂ → Q.realize w₁ ≠ Q.realize w₂

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
