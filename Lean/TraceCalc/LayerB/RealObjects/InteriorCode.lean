import TraceCalc.LayerB.RealObjects.EquivComponents
import Mathlib.Data.List.OfFn

/-!
# Real-objects formalization: canonical interior code (Phase 9 items 9a–9d)

**Phase 9 items 9a–9d (2026-04-24).** Construct the *interior side* of
the residue admin quotient realization — the "easy" half of the
boundary/interior split from items 8v–8z. The residue interior is the
strict-equality part of `RecordStructEquiv`, captured by
`FrontierWord.InteriorEquiv` (item 8v): all eight strict fields,
parameterized over `Fin n` via `Fin.cast n_eq`.

## Items in this file

* **9a** — `InteriorCodeData setup`: a non-dependent target type that
  holds canonical serializations of the seven interior strict fields
  (`X` and `externalIn` directly; the five `Fin n`-indexed fields as
  `List.ofFn` of the residue's per-position data; the dep adjacency
  as a nested `List.ofFn`). The packet count `n` is recovered from
  any of the lists' lengths — no explicit `n` field is needed, which
  removes all dependent-type bookkeeping from the target.
* **9b** — `interiorCanonicalCode : FrontierWord setup → InteriorCodeData setup`:
  the direct canonical interior code; together with two soundness/
  completeness theorems `interiorCanonicalCode_sound` /
  `interiorCanonicalCode_complete`.
* **9c (NOT NEEDED)** — A sigma-packed dependent fallback was
  considered in the user's instructions but the direct
  `List.ofFn`-based encoding succeeds: equality of `List.ofFn f₁` and
  `List.ofFn f₂` recovers both the length equality (`n_eq`) and the
  pointwise equality (modulo `Fin.cast n_eq`) without any sigma
  bookkeeping.
* **9d** — Manuscript-facing aliases `theorem_interior_code_sound`,
  `theorem_interior_code_complete`,
  `theorem_interior_code_contract_constructed`, plus a fully assembled
  `InteriorCodeContract` instance `interiorCanonicalContract`.

## Honest scope (per user's stop conditions)

* The boundary side (`BoundaryCodeContract`) is **not** touched
  except as an input — no `FrontierQuotientRealization` is claimed
  here, since the assembly theorem `component_codes_to_quotient_realization`
  (item 8y) requires both contracts.
* No canonical data is invented beyond what `InteriorEquiv` already
  exposes — the seven strict fields are reproduced verbatim, with the
  `Fin n`-indexed ones serialized via `List.ofFn` (an order-preserving
  bijection on the indexing).
* `FrontierWord` is **not** enriched.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`).
* L1098 (`def:completed-reconstruction-record`).
* L1108–L1120 (the strict-equality residue fields canonicalized here).
-/

universe u v

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ## Item 9a — Interior code target -/

/-- **`InteriorCodeData setup`** (item 9a): the target type for the
canonical interior code.

Holds a non-dependent serialization of the seven interior fields of
the residue:

* `X` and `externalIn` directly (independent of `n`).
* `packetIn`, `packetOut`, `packets`, `attach`: as `List`s in
  positional order (their length recovers `n`).
* `depEdge`: as a nested `List` (the adjacency matrix in row-major
  order, with each row a `List Bool` of length `n`).

This non-dependent shape is deliberate: it removes the `Fin.cast`
bookkeeping that would otherwise plague a dependent code. The
packet count `n` is recovered from the length of any of the
positional lists. -/
structure InteriorCodeData (setup : RewriteCalculusSetup.{u}) where
  /-- Source boundary object `X` (`def:completed-reconstruction-record` L1102). -/
  X : setup.BoundaryObject
  /-- External-input ports (clause (a) of `def:completed-reconstruction-record`,
  L1108). -/
  externalIn : List setup.RefinedInterface
  /-- Per-packet input ports, in positional order. -/
  packetIn : List (List setup.RefinedInterface)
  /-- Per-packet output ports, in positional order. -/
  packetOut : List (List setup.RefinedInterface)
  /-- Packets, in positional order. -/
  packets : List (Packet setup)
  /-- Dependency adjacency, in row-major order. -/
  depEdge : List (List Bool)
  /-- Attach witnesses, in positional order. -/
  attach : List setup.GluingWitness

/-! ## Item 9b — Direct canonical interior code -/

/-- **Item 9b**: the canonical interior code.

Maps a `FrontierWord` to the non-dependent serialization of its
seven interior fields. Each `Fin n`-indexed field is realized via
`List.ofFn`, which is a bijection between `Fin n → α` and
`{ ℓ : List α // ℓ.length = n }` (extensionality is
`List.ofFn_inj`). -/
def interiorCanonicalCode (w : FrontierWord setup) : InteriorCodeData setup :=
  { X := w.residue.X
    externalIn := w.residue.ports.externalIn
    packetIn := List.ofFn w.residue.ports.packetIn
    packetOut := List.ofFn w.residue.ports.packetOut
    packets := List.ofFn w.residue.packets
    depEdge :=
      List.ofFn (fun i : Fin w.residue.n =>
        List.ofFn (fun j : Fin w.residue.n => w.residue.dep.edge i j))
    attach := List.ofFn w.residue.attach }

/-! ### Auxiliary lemmas about `List.ofFn` across distinct lengths

These two lemmas package the only nontrivial bookkeeping for the
soundness/completeness pair: relating `List.ofFn f₁ = List.ofFn f₂`
for `f₁ : Fin n₁ → α`, `f₂ : Fin n₂ → α` to the pointwise relation
`f₁ i = f₂ (Fin.cast n_eq i)`. -/

/-- From a pointwise equality `f₁ i = f₂ (Fin.cast h i)` (with
`h : n₁ = n₂`), the corresponding `List.ofFn`s are equal. -/
private lemma list_ofFn_eq_of_cast {α : Type*} {n₁ n₂ : Nat}
    (h : n₁ = n₂) {f₁ : Fin n₁ → α} {f₂ : Fin n₂ → α}
    (heq : ∀ i, f₁ i = f₂ (Fin.cast h i)) :
    List.ofFn f₁ = List.ofFn f₂ := by
  subst h
  exact List.ofFn_inj.mpr (funext heq)

/-- From `List.ofFn f₁ = List.ofFn f₂`, the lengths agree. -/
private lemma n_eq_of_list_ofFn_eq {α : Type*} {n₁ n₂ : Nat}
    {f₁ : Fin n₁ → α} {f₂ : Fin n₂ → α}
    (h : List.ofFn f₁ = List.ofFn f₂) : n₁ = n₂ := by
  have := congrArg List.length h
  simpa [List.length_ofFn] using this

/-- From `List.ofFn f₁ = List.ofFn f₂` together with the length
equality `n_eq`, recover the pointwise relation
`f₁ i = f₂ (Fin.cast n_eq i)`. -/
private lemma cast_pointwise_of_list_ofFn_eq {α : Type*} {n₁ n₂ : Nat}
    (n_eq : n₁ = n₂) {f₁ : Fin n₁ → α} {f₂ : Fin n₂ → α}
    (h : List.ofFn f₁ = List.ofFn f₂) (i : Fin n₁) :
    f₁ i = f₂ (Fin.cast n_eq i) := by
  subst n_eq
  have hf : f₁ = f₂ := List.ofFn_inj.mp h
  simp [hf]

/-! ### Soundness and completeness of the canonical interior code -/

/-- **Item 9b (soundness)**: `InteriorEquiv` ⇒ equal interior codes. -/
theorem interiorCanonicalCode_sound {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.InteriorEquiv w₁ w₂) :
    interiorCanonicalCode w₁ = interiorCanonicalCode w₂ := by
  unfold interiorCanonicalCode
  refine ?_
  congr 1
  · exact h.X_eq
  · exact h.externalIn_eq
  · exact list_ofFn_eq_of_cast h.n_eq h.packetIn_eq
  · exact list_ofFn_eq_of_cast h.n_eq h.packetOut_eq
  · exact list_ofFn_eq_of_cast h.n_eq h.packets_eq
  · refine list_ofFn_eq_of_cast h.n_eq ?_
    intro i
    refine list_ofFn_eq_of_cast h.n_eq ?_
    intro j
    exact h.dep_edge_eq i j
  · exact list_ofFn_eq_of_cast h.n_eq h.attach_eq

/-- **Item 9b (completeness)**: equal interior codes ⇒
`InteriorEquiv`. -/
theorem interiorCanonicalCode_complete {w₁ w₂ : FrontierWord setup}
    (h : interiorCanonicalCode w₁ = interiorCanonicalCode w₂) :
    FrontierWord.InteriorEquiv w₁ w₂ := by
  -- Project the seven field equalities out of `h`.
  have hX : w₁.residue.X = w₂.residue.X :=
    congrArg InteriorCodeData.X h
  have heI : w₁.residue.ports.externalIn = w₂.residue.ports.externalIn :=
    congrArg InteriorCodeData.externalIn h
  have hpI :
      List.ofFn w₁.residue.ports.packetIn
        = List.ofFn w₂.residue.ports.packetIn :=
    congrArg InteriorCodeData.packetIn h
  have hpO :
      List.ofFn w₁.residue.ports.packetOut
        = List.ofFn w₂.residue.ports.packetOut :=
    congrArg InteriorCodeData.packetOut h
  have hp :
      List.ofFn w₁.residue.packets = List.ofFn w₂.residue.packets :=
    congrArg InteriorCodeData.packets h
  have hdE :
      List.ofFn (fun i : Fin w₁.residue.n =>
          List.ofFn (fun j : Fin w₁.residue.n => w₁.residue.dep.edge i j))
        = List.ofFn (fun i : Fin w₂.residue.n =>
          List.ofFn (fun j : Fin w₂.residue.n => w₂.residue.dep.edge i j)) :=
    congrArg InteriorCodeData.depEdge h
  have ha :
      List.ofFn w₁.residue.attach = List.ofFn w₂.residue.attach :=
    congrArg InteriorCodeData.attach h
  -- Recover `n_eq` from the length of any positional list (use `packets`).
  have n_eq : w₁.residue.n = w₂.residue.n :=
    n_eq_of_list_ofFn_eq hp
  refine
    { n_eq := n_eq
      X_eq := hX
      externalIn_eq := heI
      packetIn_eq := ?_
      packetOut_eq := ?_
      packets_eq := ?_
      dep_edge_eq := ?_
      attach_eq := ?_ }
  · intro i
    exact cast_pointwise_of_list_ofFn_eq n_eq hpI i
  · intro i
    exact cast_pointwise_of_list_ofFn_eq n_eq hpO i
  · intro i
    exact cast_pointwise_of_list_ofFn_eq n_eq hp i
  · intro i j
    have h_outer :
        List.ofFn (fun j : Fin w₁.residue.n => w₁.residue.dep.edge i j)
          = List.ofFn (fun j : Fin w₂.residue.n =>
              w₂.residue.dep.edge (Fin.cast n_eq i) j) :=
      cast_pointwise_of_list_ofFn_eq n_eq hdE i
    exact cast_pointwise_of_list_ofFn_eq n_eq h_outer j
  · intro i
    exact cast_pointwise_of_list_ofFn_eq n_eq ha i

/-! ## Item 9d — Assembled contract and manuscript-facing aliases -/

/-- **Item 9d (constructed contract)**: the canonical interior code
is a fully assembled `InteriorCodeContract`.

This is the *real* (non-`Prop`-placeholder, non-obligation)
discharge of the interior side of the residue admin quotient
realization split (item 8x). -/
def interiorCanonicalContract :
    InteriorCodeContract.{u, u} setup where
  InteriorCode := InteriorCodeData setup
  interiorCode := interiorCanonicalCode
  sound := interiorCanonicalCode_sound
  complete := interiorCanonicalCode_complete

/-- **Audit theorem (9d)**: the assembled contract's `interiorCode`
is `interiorCanonicalCode`. -/
@[simp] theorem interiorCanonicalContract_interiorCode
    (w : FrontierWord setup) :
    interiorCanonicalContract.interiorCode w = interiorCanonicalCode w :=
  rfl

/-- **Manuscript alias (9d.a)**: the soundness half of the interior
code contract. -/
theorem theorem_interior_code_sound {w₁ w₂ : FrontierWord setup}
    (h : FrontierWord.InteriorEquiv w₁ w₂) :
    interiorCanonicalCode w₁ = interiorCanonicalCode w₂ :=
  interiorCanonicalCode_sound h

/-- **Manuscript alias (9d.b)**: the completeness half of the
interior code contract. -/
theorem theorem_interior_code_complete {w₁ w₂ : FrontierWord setup}
    (h : interiorCanonicalCode w₁ = interiorCanonicalCode w₂) :
    FrontierWord.InteriorEquiv w₁ w₂ :=
  interiorCanonicalCode_complete h

/-- **Manuscript alias (9d.c)**: the interior-code contract is
*constructed* (no longer an obligation). -/
def theorem_interior_code_contract_constructed
    (setup : RewriteCalculusSetup.{u}) :
    InteriorCodeContract.{u, u} setup :=
  interiorCanonicalContract (setup := setup)

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
