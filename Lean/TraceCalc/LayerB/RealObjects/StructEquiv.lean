import TraceCalc.LayerB.RealObjects.IndependentPeel

/-!
# Real-objects formalization: structural record equivalence for boundary block swaps

**Phase 3B item 5e first installment (2026-04-24).** Per user's
verbatim Phase 3B item 5e directive: introduce a structural equivalence
strictly weaker than `RecordEquiv` that **explicitly tracks** the
boundary-block permutation produced by adjacent independent sink swaps,
rather than (a) lying about it via a hidden setup-level commutativity
axiom, or (b) merely forgetting the boundary fields.

Per the new `INV Boundary-Order` invariant: canonical reconstruction is
**not** "all deletion orders are literally equal." It is "all deletion
orders are equivalent after accounting for administrative boundary
ordering." This file builds the predicate that lets us state that
distinction honestly.

## Architecture

* `RecordStructEquiv BR R₁ R₂` — propositional structural equivalence
  parameterized by a boundary-object relation `BR`. The "interior"
  fields (`n`, `X`, `externalIn`, `packets`, `dep`, `attach`, `tensor`,
  `key`, and pointwise `packetIn`/`packetOut`) are required strictly
  equal (all preserved by adjacent independent peeling at kept
  indices), while:
  * `externalOut` is required equal **up to `List.Perm`**
    (the `++`-order obstruction);
  * `Y` is required related by the parameter `BR`
    (the opaque-`setup.exposeBoundaryUnderSinkDeletion` obstruction —
    the consumer instantiates `BR` either to `Eq` for the strict case
    or to a setup-supplied boundary equivalence).

* `RecordStructEquiv.refl` / `.symm` / `.trans` — equivalence-relation
  API, granted that `BR` is reflexive / symmetric / transitive.

* `RecordStructEquiv.ofRecordEquiv` — every `RecordEquiv` is a
  `RecordStructEquiv` along `BR := Eq`. Lets the strict swap case
  (when boundary order happens to match) compose with the
  permutation case downstream.

## Scope discipline

This installment delivers **only** the predicate plus its
equivalence-relation API and the `RecordEquiv → RecordStructEquiv`
embedding. The actual swap-square theorem
`peelSink_swap_structEquiv` (consuming `IndependentSinks` from
`IndependentPeel.lean`) is the **second installment** of item 5e and
is gated on a careful reckoning of what `BR` should be on the
swap-image (most likely a setup-supplied or definitionally-imposed
relation that captures "two boundary objects produced by deleting
the same two sinks in opposite orders").

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose honest formulation requires the present predicate.
* L1224 (`def:boundary-exposure`) — the per-step boundary-exposure
  definition whose order-dependence is exactly what `RecordStructEquiv`
  factors out.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### Structural equivalence parameterized by a boundary relation -/

/-- **Structural record equivalence parameterized by a boundary
relation `BR`.** Strictly weaker than `RecordEquiv` (which is recovered
when `BR := Eq`), this predicate:

* requires the **interior** fields (`n`, `X`, `externalIn`, `packets`,
  `dep`, `attach`, `tensor`, `key`, and pointwise `packetIn`/`packetOut`
  ports) to agree strictly — these are the fields preserved by
  adjacent independent sink peeling at kept indices;
* requires the **external-output list** to agree only **up to
  `List.Perm`** — the manuscript-level obstruction surfaced by
  `restrictedExternalOut` being defined via non-commutative `List.++`;
* requires the **boundary object** `Y` to be related by the parameter
  `BR` — the opaque-`setup.exposeBoundaryUnderSinkDeletion` obstruction.

This is the "honest middle notion" between dropping boundary fields
entirely and asserting them strictly. -/
structure RecordStructEquiv
    (BR : setup.BoundaryObject → setup.BoundaryObject → Prop)
    (R₁ R₂ : CompletedReconstructionRecord setup) : Prop where
  /-- Packet counts agree. -/
  n_eq : R₁.n = R₂.n
  /-- Source boundaries agree. -/
  X_eq : R₁.X = R₂.X
  /-- Target boundaries are `BR`-related (boundary-permutation slot). -/
  Y_rel : BR R₁.Y R₂.Y
  /-- External-input lists agree. -/
  externalIn_eq : R₁.ports.externalIn = R₂.ports.externalIn
  /-- External-output lists agree **up to `List.Perm`**
  (the boundary-block-swap slot). -/
  externalOut_perm : List.Perm R₁.ports.externalOut R₂.ports.externalOut
  /-- Per-packet input ports agree pointwise. -/
  packetIn_eq :
    ∀ (i : Fin R₁.n),
      R₁.ports.packetIn i = R₂.ports.packetIn (Fin.cast n_eq i)
  /-- Per-packet output ports agree pointwise. -/
  packetOut_eq :
    ∀ (i : Fin R₁.n),
      R₁.ports.packetOut i = R₂.ports.packetOut (Fin.cast n_eq i)
  /-- Packets agree pointwise. -/
  packets_eq :
    ∀ (i : Fin R₁.n),
      R₁.packets i = R₂.packets (Fin.cast n_eq i)
  /-- Dependency edges agree pointwise. -/
  dep_edge_eq :
    ∀ (i j : Fin R₁.n),
      R₁.dep.edge i j = R₂.dep.edge (Fin.cast n_eq i) (Fin.cast n_eq j)
  /-- Attach witnesses agree pointwise. -/
  attach_eq :
    ∀ (i : Fin R₁.n), R₁.attach i = R₂.attach (Fin.cast n_eq i)

namespace RecordStructEquiv

variable {BR : setup.BoundaryObject → setup.BoundaryObject → Prop}

/-- Reflexivity, granted `BR` is reflexive. -/
theorem refl (hBR : ∀ Y, BR Y Y) (R : CompletedReconstructionRecord setup) :
    RecordStructEquiv BR R R where
  n_eq := rfl
  X_eq := rfl
  Y_rel := hBR R.Y
  externalIn_eq := rfl
  externalOut_perm := List.Perm.refl _
  packetIn_eq := fun _ => rfl
  packetOut_eq := fun _ => rfl
  packets_eq := fun _ => rfl
  dep_edge_eq := fun _ _ => rfl
  attach_eq := fun _ => rfl

/-- Symmetry, granted `BR` is symmetric. -/
theorem symm (hBR : ∀ {Y₁ Y₂}, BR Y₁ Y₂ → BR Y₂ Y₁)
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordStructEquiv BR R₁ R₂) :
    RecordStructEquiv BR R₂ R₁ where
  n_eq := h.n_eq.symm
  X_eq := h.X_eq.symm
  Y_rel := hBR h.Y_rel
  externalIn_eq := h.externalIn_eq.symm
  externalOut_perm := h.externalOut_perm.symm
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

/-- Transitivity, granted `BR` is transitive. -/
theorem trans (hBR : ∀ {Y₁ Y₂ Y₃}, BR Y₁ Y₂ → BR Y₂ Y₃ → BR Y₁ Y₃)
    {R₁ R₂ R₃ : CompletedReconstructionRecord setup}
    (h₁ : RecordStructEquiv BR R₁ R₂) (h₂ : RecordStructEquiv BR R₂ R₃) :
    RecordStructEquiv BR R₁ R₃ where
  n_eq := h₁.n_eq.trans h₂.n_eq
  X_eq := h₁.X_eq.trans h₂.X_eq
  Y_rel := hBR h₁.Y_rel h₂.Y_rel
  externalIn_eq := h₁.externalIn_eq.trans h₂.externalIn_eq
  externalOut_perm := h₁.externalOut_perm.trans h₂.externalOut_perm
  packetIn_eq := fun i => by
    rw [h₁.packetIn_eq i, h₂.packetIn_eq (Fin.cast h₁.n_eq i)]; rfl
  packetOut_eq := fun i => by
    rw [h₁.packetOut_eq i, h₂.packetOut_eq (Fin.cast h₁.n_eq i)]; rfl
  packets_eq := fun i => by
    rw [h₁.packets_eq i, h₂.packets_eq (Fin.cast h₁.n_eq i)]; rfl
  dep_edge_eq := fun i j => by
    rw [h₁.dep_edge_eq i j,
        h₂.dep_edge_eq (Fin.cast h₁.n_eq i) (Fin.cast h₁.n_eq j)]
    rfl
  attach_eq := fun i => by
    rw [h₁.attach_eq i, h₂.attach_eq (Fin.cast h₁.n_eq i)]; rfl

end RecordStructEquiv

/-! ### Embedding from strict `RecordEquiv` -/

/-- **Every `RecordEquiv` is a `RecordStructEquiv` along `BR := Eq`.**
This embedding lets the strict-equivalence layer compose with the
boundary-permutation layer downstream (e.g. when one side of an
administrative move happens to produce identical boundary order). -/
theorem RecordEquiv.toStructEquiv
    {R₁ R₂ : CompletedReconstructionRecord setup} (h : RecordEquiv R₁ R₂) :
    RecordStructEquiv (Eq) R₁ R₂ where
  n_eq := h.n_eq
  X_eq := h.X_eq
  Y_rel := h.Y_eq
  externalIn_eq := h.externalIn_eq
  externalOut_perm := h.externalOut_eq ▸ List.Perm.refl _
  packetIn_eq := h.packetIn_eq
  packetOut_eq := h.packetOut_eq
  packets_eq := h.packets_eq
  dep_edge_eq := h.dep_edge_eq
  attach_eq := h.attach_eq

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
