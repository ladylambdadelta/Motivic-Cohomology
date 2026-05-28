import TraceCalc.LayerB.RealObjects.CanonicalFrontierWord
import TraceCalc.LayerC.RealObjects.QuotientRealization

/-!
# Real-objects formalization: boundary/interior split of `FrontierWord.Equiv` (items 8v–8z)

**Phase 8 items 8v–8z (2026-04-24).** Refine `FrontierWord.Equiv` into
named boundary and interior components so that boundary/interior code
completeness obligations can receive *real theorem signatures*
(replacing the `Prop` placeholders from item 8q).

## Items in this file

* **8v** — `FrontierWord.BoundaryEquiv` (the boundary slot:
  `BoundaryAdminEquiv` on `Y`, `List.Perm` on `externalOut`) and
  `FrontierWord.InteriorEquiv` (everything else: `n_eq` plus
  `X_eq`/`externalIn_eq`/`packetIn_eq`/`packetOut_eq`/`packets_eq`/
  `dep_edge_eq`/`attach_eq`).
* **8w** — `FrontierWord.equiv_iff_boundary_and_interior`: the iff
  decomposition of the total equivalence.
* **8x** — `BoundaryCodeContract` and `InteriorCodeContract`:
  per-component coding contracts with both `sound` and `complete`
  carrying *real signatures* (no `Prop` placeholders).
* **8y** — `component_codes_to_quotient_realization`: assembling the
  two component contracts into a `FrontierQuotientRealization`.
* **8z** — Manuscript-facing aliases.

## Honest scope (per user's stop conditions, all honored)

* The meaning of `FrontierWord.Equiv` is **not** changed —
  `BoundaryEquiv ∧ InteriorEquiv` is iff-equivalent to it; the
  components are honest projections of `RecordStructEquiv`.
* A first honest concrete boundary/interior code route is supplied by
  quotienting directly by `BoundaryEquiv` and `InteriorEquiv`.
* No semantic or extensional boundary/interior code is constructed
  beyond those quotient carriers.
* `FrontierWord` is **not** enriched.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`).
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 8v — Component equivalence predicates -/

namespace FrontierWord

/-- **`FrontierWord.BoundaryEquiv`** (item 8v, boundary half): the
boundary-admin slot of `FrontierWord.Equiv`.

Captures exactly the fields of `RecordStructEquiv BoundaryAdminEquiv`
that are *not* asserted by strict equality: the boundary object
related under `BoundaryAdminEquiv`, and the external-output list up
to `List.Perm`. -/
structure BoundaryEquiv (w₁ w₂ : FrontierWord setup) : Prop where
  /-- Target boundaries are `BoundaryAdminEquiv`-related. -/
  Y_rel : BoundaryAdminEquiv w₁.residue.Y w₂.residue.Y
  /-- External-output lists agree up to `List.Perm`. -/
  externalOut_perm :
    List.Perm w₁.residue.ports.externalOut w₂.residue.ports.externalOut

/-- Reflexivity of the boundary component relation. -/
theorem BoundaryEquiv.refl (w : FrontierWord setup) : BoundaryEquiv w w where
  Y_rel := BoundaryAdminEquiv.refl _
  externalOut_perm := List.Perm.refl _

/-- Symmetry of the boundary component relation. -/
theorem BoundaryEquiv.symm {w₁ w₂ : FrontierWord setup}
    (h : BoundaryEquiv w₁ w₂) : BoundaryEquiv w₂ w₁ where
  Y_rel := BoundaryAdminEquiv.symm h.Y_rel
  externalOut_perm := h.externalOut_perm.symm

/-- Transitivity of the boundary component relation. -/
theorem BoundaryEquiv.trans {w₁ w₂ w₃ : FrontierWord setup}
    (h₁ : BoundaryEquiv w₁ w₂) (h₂ : BoundaryEquiv w₂ w₃) :
    BoundaryEquiv w₁ w₃ where
  Y_rel := BoundaryAdminEquiv.trans h₁.Y_rel h₂.Y_rel
  externalOut_perm := h₁.externalOut_perm.trans h₂.externalOut_perm

/-- **`FrontierWord.InteriorEquiv`** (item 8v, interior half): the
strict-equality slot of `FrontierWord.Equiv`.

Captures all `RecordStructEquiv` fields asserted by `=`. The
packet-count equality `n_eq` is included on the interior side
because every other strict equality is parameterized over `Fin n`
and uses `Fin.cast n_eq`. -/
structure InteriorEquiv (w₁ w₂ : FrontierWord setup) : Prop where
  /-- Packet counts agree. -/
  n_eq : w₁.residue.n = w₂.residue.n
  /-- Source boundaries agree. -/
  X_eq : w₁.residue.X = w₂.residue.X
  /-- External-input lists agree. -/
  externalIn_eq :
    w₁.residue.ports.externalIn = w₂.residue.ports.externalIn
  /-- Per-packet input ports agree pointwise. -/
  packetIn_eq :
    ∀ (i : Fin w₁.residue.n),
      w₁.residue.ports.packetIn i
        = w₂.residue.ports.packetIn (Fin.cast n_eq i)
  /-- Per-packet output ports agree pointwise. -/
  packetOut_eq :
    ∀ (i : Fin w₁.residue.n),
      w₁.residue.ports.packetOut i
        = w₂.residue.ports.packetOut (Fin.cast n_eq i)
  /-- Packets agree pointwise. -/
  packets_eq :
    ∀ (i : Fin w₁.residue.n),
      w₁.residue.packets i
        = w₂.residue.packets (Fin.cast n_eq i)
  /-- Dependency edges agree pointwise. -/
  dep_edge_eq :
    ∀ (i j : Fin w₁.residue.n),
      w₁.residue.dep.edge i j
        = w₂.residue.dep.edge (Fin.cast n_eq i) (Fin.cast n_eq j)
  /-- Attach witnesses agree pointwise. -/
  attach_eq :
    ∀ (i : Fin w₁.residue.n),
      w₁.residue.attach i = w₂.residue.attach (Fin.cast n_eq i)

/-- Reflexivity of the interior component relation. -/
theorem InteriorEquiv.refl (w : FrontierWord setup) : InteriorEquiv w w where
  n_eq := rfl
  X_eq := rfl
  externalIn_eq := rfl
  packetIn_eq := fun _ => rfl
  packetOut_eq := fun _ => rfl
  packets_eq := fun _ => rfl
  dep_edge_eq := fun _ _ => rfl
  attach_eq := fun _ => rfl

/-- Symmetry of the interior component relation. -/
theorem InteriorEquiv.symm {w₁ w₂ : FrontierWord setup}
    (h : InteriorEquiv w₁ w₂) : InteriorEquiv w₂ w₁ where
  n_eq := h.n_eq.symm
  X_eq := h.X_eq.symm
  externalIn_eq := h.externalIn_eq.symm
  packetIn_eq := fun i => by
    have h' := (h.packetIn_eq (Fin.cast h.n_eq.symm i)).symm
    convert h' using 2
  packetOut_eq := fun i => by
    have h' := (h.packetOut_eq (Fin.cast h.n_eq.symm i)).symm
    convert h' using 2
  packets_eq := fun i => by
    have h' := (h.packets_eq (Fin.cast h.n_eq.symm i)).symm
    convert h' using 2
  dep_edge_eq := fun i j => by
    have h' := (h.dep_edge_eq (Fin.cast h.n_eq.symm i) (Fin.cast h.n_eq.symm j)).symm
    convert h' using 2
  attach_eq := fun i => by
    have h' := (h.attach_eq (Fin.cast h.n_eq.symm i)).symm
    convert h' using 2

/-- Transitivity of the interior component relation. -/
theorem InteriorEquiv.trans {w₁ w₂ w₃ : FrontierWord setup}
    (h₁ : InteriorEquiv w₁ w₂) (h₂ : InteriorEquiv w₂ w₃) :
    InteriorEquiv w₁ w₃ where
  n_eq := h₁.n_eq.trans h₂.n_eq
  X_eq := h₁.X_eq.trans h₂.X_eq
  externalIn_eq := h₁.externalIn_eq.trans h₂.externalIn_eq
  packetIn_eq := fun i => by
    rw [h₁.packetIn_eq i, h₂.packetIn_eq (Fin.cast h₁.n_eq i)]
    rfl
  packetOut_eq := fun i => by
    rw [h₁.packetOut_eq i, h₂.packetOut_eq (Fin.cast h₁.n_eq i)]
    rfl
  packets_eq := fun i => by
    rw [h₁.packets_eq i, h₂.packets_eq (Fin.cast h₁.n_eq i)]
    rfl
  dep_edge_eq := fun i j => by
    rw [h₁.dep_edge_eq i j,
      h₂.dep_edge_eq (Fin.cast h₁.n_eq i) (Fin.cast h₁.n_eq j)]
    rfl
  attach_eq := fun i => by
    rw [h₁.attach_eq i, h₂.attach_eq (Fin.cast h₁.n_eq i)]
    rfl

/-- Setoid on frontier words induced by the boundary component relation. -/
def boundarySetoid (setup : RewriteCalculusSetup.{u}) : Setoid (FrontierWord setup) where
  r := BoundaryEquiv
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact BoundaryEquiv.refl w
    · intro w₁ w₂ h
      exact BoundaryEquiv.symm h
    · intro w₁ w₂ w₃ h₁ h₂
      exact BoundaryEquiv.trans h₁ h₂

/-- Setoid on frontier words induced by the interior component relation. -/
def interiorSetoid (setup : RewriteCalculusSetup.{u}) : Setoid (FrontierWord setup) where
  r := InteriorEquiv
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro w
      exact InteriorEquiv.refl w
    · intro w₁ w₂ h
      exact InteriorEquiv.symm h
    · intro w₁ w₂ w₃ h₁ h₂
      exact InteriorEquiv.trans h₁ h₂

/-- Quotient carrier for the boundary component of frontier equivalence. -/
def BoundaryEquivClass (setup : RewriteCalculusSetup.{u}) : Type u :=
  Quotient (boundarySetoid setup)

/-- Constructor for a frontier word's boundary-equivalence class. -/
def BoundaryEquivClass.mk {setup : RewriteCalculusSetup.{u}}
    (w : FrontierWord setup) : BoundaryEquivClass setup :=
  Quotient.mk (boundarySetoid setup) w

/-- Quotient carrier for the interior component of frontier equivalence. -/
def InteriorEquivClass (setup : RewriteCalculusSetup.{u}) : Type u :=
  Quotient (interiorSetoid setup)

/-- Constructor for a frontier word's interior-equivalence class. -/
def InteriorEquivClass.mk {setup : RewriteCalculusSetup.{u}}
    (w : FrontierWord setup) : InteriorEquivClass setup :=
  Quotient.mk (interiorSetoid setup) w

/-! ## Item 8w — Equiv iff components -/

/-- **Item 8w**: `FrontierWord.Equiv` decomposes as the conjunction
of its boundary and interior components.

The proof is by destructuring the `RecordStructEquiv` fields into
the two component groups, and re-assembling. **No content
manufactured** — `RecordStructEquiv` is a record, the two
components are honest projections. -/
theorem equiv_iff_boundary_and_interior {w₁ w₂ : FrontierWord setup} :
    FrontierWord.Equiv w₁ w₂ ↔
      BoundaryEquiv w₁ w₂ ∧ InteriorEquiv w₁ w₂ := by
  constructor
  · intro h
    refine ⟨⟨h.Y_rel, h.externalOut_perm⟩,
      ⟨h.n_eq, h.X_eq, h.externalIn_eq, h.packetIn_eq, h.packetOut_eq,
        h.packets_eq, h.dep_edge_eq, h.attach_eq⟩⟩
  · rintro ⟨⟨hY, hOut⟩, hI⟩
    exact
      { n_eq := hI.n_eq
        X_eq := hI.X_eq
        Y_rel := hY
        externalIn_eq := hI.externalIn_eq
        externalOut_perm := hOut
        packetIn_eq := hI.packetIn_eq
        packetOut_eq := hI.packetOut_eq
        packets_eq := hI.packets_eq
        dep_edge_eq := hI.dep_edge_eq
        attach_eq := hI.attach_eq }

/-- **Forward projection**: `Equiv → BoundaryEquiv`. -/
theorem Equiv.toBoundaryEquiv {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) : BoundaryEquiv w₁ w₂ :=
  ((equiv_iff_boundary_and_interior).mp h).1

/-- **Forward projection**: `Equiv → InteriorEquiv`. -/
theorem Equiv.toInteriorEquiv {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.Equiv w₁ w₂) : InteriorEquiv w₁ w₂ :=
  ((equiv_iff_boundary_and_interior).mp h).2

/-- **Backward assembly**: components ⇒ total. -/
theorem Equiv.ofComponents {w₁ w₂ : FrontierWord setup}
    (hB : BoundaryEquiv w₁ w₂) (hI : InteriorEquiv w₁ w₂) :
    FrontierWord.Equiv w₁ w₂ :=
  (equiv_iff_boundary_and_interior).mpr ⟨hB, hI⟩

end FrontierWord

/-! ## Item 8x — Real-signature component code contracts -/

/-- **`BoundaryCodeContract setup`** (item 8x): a coding contract
for the *boundary component* of `FrontierWord.Equiv`.

Both `sound` and `complete` carry **real signatures** (no `Prop`
placeholders): they relate `boundaryCode` equality with
`FrontierWord.BoundaryEquiv`. -/
structure BoundaryCodeContract (setup : RewriteCalculusSetup.{u}) where
  /-- The boundary-code target type. -/
  BoundaryCode : Type v
  /-- The boundary code function. -/
  boundaryCode : FrontierWord setup → BoundaryCode
  /-- Soundness: `BoundaryEquiv` ⇒ equal boundary codes. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.BoundaryEquiv w₁ w₂ → boundaryCode w₁ = boundaryCode w₂
  /-- **Completeness with a real signature**: equal boundary codes
  imply boundary equivalence. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      boundaryCode w₁ = boundaryCode w₂ → FrontierWord.BoundaryEquiv w₁ w₂

/-- **`InteriorCodeContract setup`** (item 8x): the analogous coding
contract for the *interior component*. Both `sound` and `complete`
carry real signatures. -/
structure InteriorCodeContract (setup : RewriteCalculusSetup.{u}) where
  /-- The interior-code target type. -/
  InteriorCode : Type v
  /-- The interior code function. -/
  interiorCode : FrontierWord setup → InteriorCode
  /-- Soundness: `InteriorEquiv` ⇒ equal interior codes. -/
  sound :
    ∀ {w₁ w₂ : FrontierWord setup},
      FrontierWord.InteriorEquiv w₁ w₂ → interiorCode w₁ = interiorCode w₂
  /-- **Completeness with a real signature**: equal interior codes
  imply interior equivalence. -/
  complete :
    ∀ {w₁ w₂ : FrontierWord setup},
      interiorCode w₁ = interiorCode w₂ → FrontierWord.InteriorEquiv w₁ w₂

/-- First honest concrete boundary-code contract.

This uses the quotient of frontier words by `FrontierWord.BoundaryEquiv`.
Equal codes are exactly boundary-equivalence classes. -/
def boundaryEquivQuotientCodeContract
    (setup : RewriteCalculusSetup.{u}) : BoundaryCodeContract.{u, u} setup where
  BoundaryCode := FrontierWord.BoundaryEquivClass setup
  boundaryCode w := FrontierWord.BoundaryEquivClass.mk w
  sound h := Quotient.sound h
  complete h := Quotient.exact h

/-- First honest concrete interior-code contract.

This uses the quotient of frontier words by `FrontierWord.InteriorEquiv`.
Equal codes are exactly interior-equivalence classes. -/
def interiorEquivQuotientCodeContract
    (setup : RewriteCalculusSetup.{u}) : InteriorCodeContract.{u, u} setup where
  InteriorCode := FrontierWord.InteriorEquivClass setup
  interiorCode w := FrontierWord.InteriorEquivClass.mk w
  sound h := Quotient.sound h
  complete h := Quotient.exact h

/-! ## Item 8y — Assemble quotient realization from component contracts -/

/-- **Item 8y**: a boundary-code contract and an interior-code
contract together assemble into a faithful `FrontierQuotientRealization`,
using the `BoundaryEquiv ∧ InteriorEquiv ↔ Equiv` decomposition
(item 8w).

The realize-target is `BoundaryCode × InteriorCode`. The proof is
elementary:

* `respects_equiv`: project a total `Equiv` to its components and
  apply the per-component soundness obligations.
* `faithful`: project the product equality to per-side equalities
  and apply the per-component completeness obligations to obtain
  the components, then reassemble. **No content manufactured**. -/
def component_codes_to_quotient_realization
    (B : BoundaryCodeContract.{u, v} setup)
    (I : InteriorCodeContract.{u, v} setup) :
    FrontierQuotientRealization.{u, v} setup where
  Target := B.BoundaryCode × I.InteriorCode
  realize w := (B.boundaryCode w, I.interiorCode w)
  respects_equiv h := by
    have hB := h.toBoundaryEquiv
    have hI := h.toInteriorEquiv
    exact Prod.mk.injEq .. |>.mpr ⟨B.sound hB, I.sound hI⟩
  faithful h := by
    have hb : B.boundaryCode _ = B.boundaryCode _ := congrArg Prod.fst h
    have hi : I.interiorCode _ = I.interiorCode _ := congrArg Prod.snd h
    exact FrontierWord.Equiv.ofComponents (B.complete hb) (I.complete hi)

/-- **Audit theorem (8y.b)**: the component-codes assembly's
`realize` is the obvious pair. -/
@[simp] theorem component_codes_to_quotient_realization_realize
    (B : BoundaryCodeContract.{u, v} setup)
    (I : InteriorCodeContract.{u, v} setup)
    (w : FrontierWord setup) :
    (component_codes_to_quotient_realization B I).realize w
      = (B.boundaryCode w, I.interiorCode w) :=
  rfl

/-! ## Item 8z — Manuscript-facing aliases -/

/-- **Manuscript alias (8z.a)**: the total `FrontierWord.Equiv`
splits as the conjunction of its boundary and interior components. -/
theorem theorem_frontier_equiv_splits_boundary_interior
    {w₁ w₂ : FrontierWord setup} :
    FrontierWord.Equiv w₁ w₂ ↔
      FrontierWord.BoundaryEquiv w₁ w₂ ∧ FrontierWord.InteriorEquiv w₁ w₂ :=
  FrontierWord.equiv_iff_boundary_and_interior

/-- **Manuscript alias (8z.b)**: the boundary-code contract is the
obligation `BoundaryCodeContract`. **Real-signature** completeness. -/
def theorem_boundary_code_contract (setup : RewriteCalculusSetup.{u}) :
    Type _ :=
  BoundaryCodeContract.{u, v} setup

/-- **Manuscript alias (8z.c)**: the interior-code contract is the
obligation `InteriorCodeContract`. **Real-signature** completeness. -/
def theorem_interior_code_contract (setup : RewriteCalculusSetup.{u}) :
    Type _ :=
  InteriorCodeContract.{u, v} setup

/-- **Manuscript alias (8z.d)**: a boundary-code contract and an
interior-code contract together give a faithful quotient
realization of `FrontierWord setup / FrontierWord.Equiv`. -/
def theorem_component_codes_give_quotient_realization
    (B : BoundaryCodeContract.{u, v} setup)
    (I : InteriorCodeContract.{u, v} setup) :
    FrontierQuotientRealization.{u, v} setup :=
  component_codes_to_quotient_realization B I

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
