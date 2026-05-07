import TraceCalc.LayerB.RealObjects.CompletedRecord

/-!
# Real-objects formalization: typed attachment, gluing, and boundary exposure

**Real-objects path, cycle 3 (2026-04-23).**

This file formalizes:

* `def:boundary-exposure` (`our_paper_draft.tex` L1224) as a
  record-level operation `exposeBoundaryUnderSinkDeletion`.
* The typed-interface compatibility predicate
  `IsCompatibleAttachmentForPacket` for `def:completed-reconstruction-record`
  C2 (L1128); this is the manuscript's "the attachment witnesses are
  compatible with the typed interfaces and with the ambient cirquent
  structure". Replaces the placeholder `True` C2 from cycle 2 with a
  concrete carrier-level predicate; the predicate itself is decided by
  `setup.attachmentCompatible` on `RewriteCalculusSetup`.
* A refined `IsCompletedRefined` predicate that uses the typed C2.

This file does **not**:

* Formalize the `Glue` operation at the level of certified traces (real-path
  obligation (4)); the boundary-level `setup.glueBoundary` is provided on
  `RewriteCalculusSetup` and used here for boundary-level statements only.
* State or prove `lem:sink-deletion-inverse` (L1240) or
  `lem:sink-peel-preserves-completedness` (L1206); those are real-path
  obligations (5)–(6) and require the predecessor-subrecord construction
  (next cycle).

## Manuscript-clarity flag

The manuscript characterizes `def:boundary-exposure` (L1224) constructively
in three numbered steps and asserts functoriality, but it does not give a
closed-form formula on cirquents. Concrete instantiations of
`RewriteCalculusSetup` must supply the explicit construction.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

variable (setup : RewriteCalculusSetup.{u})

/-! ### Typed-interface compatibility for an attachment witness

`def:completed-reconstruction-record` C2 (L1128) and
`def:admissibility` clause (c) (L662). -/

/-- The typed-interface compatibility predicate: an attachment witness
`w : GluingWitness` for a packet with refined input ports `ri` and
refined output ports `ro`, glued from boundary `b` to boundary `b'`, is
*compatible* if `setup.attachmentCompatible w b b' ri ro = true`.

Faithful to `def:completed-reconstruction-record` C2 (L1128): "the
attachment witnesses are compatible with the typed interfaces and with
the ambient cirquent structure". -/
def IsCompatibleAttachment
    (w : setup.GluingWitness)
    (boundaryBefore boundaryAfter : setup.BoundaryObject)
    (refinedIn refinedOut : List setup.RefinedInterface) : Prop :=
  setup.attachmentCompatible w boundaryBefore boundaryAfter
    refinedIn refinedOut = true

@[simp] theorem isCompatibleAttachment_iff
    (w : setup.GluingWitness)
    (boundaryBefore boundaryAfter : setup.BoundaryObject)
    (refinedIn refinedOut : List setup.RefinedInterface) :
    setup.IsCompatibleAttachment w boundaryBefore boundaryAfter refinedIn refinedOut ↔
      setup.attachmentCompatible w boundaryBefore boundaryAfter refinedIn refinedOut = true :=
  Iff.rfl

/-- C2 specialized to a packet inside a completed reconstruction record.

The boundary "before" is the boundary of the packet's ambient state, and
"after" is obtained by applying `setup.glueBoundary` to it using the
packet's refined ports and the recorded attachment witness. -/
def IsCompatibleAttachmentForPacket
    {R : CompletedReconstructionRecord setup} (i : Fin R.n) : Prop :=
  let P := R.packets i
  let b := setup.boundaryOf P.state
  setup.IsCompatibleAttachment (R.attach i) b
    (setup.glueBoundary b P.refinedIn P.refinedOut (R.attach i))
    P.refinedIn P.refinedOut

@[simp] theorem isCompatibleAttachmentForPacket_iff
    {R : CompletedReconstructionRecord setup} (i : Fin R.n) :
    setup.IsCompatibleAttachmentForPacket (R := R) i ↔
      setup.IsCompatibleAttachment (R.attach i)
        (setup.boundaryOf (R.packets i).state)
        (setup.glueBoundary
          (setup.boundaryOf (R.packets i).state)
          (R.packets i).refinedIn (R.packets i).refinedOut (R.attach i))
        (R.packets i).refinedIn (R.packets i).refinedOut :=
  Iff.rfl

theorem isCompatibleAttachmentForPacket_eq_attachmentCompatible
    {R : CompletedReconstructionRecord setup} (i : Fin R.n) :
    setup.IsCompatibleAttachmentForPacket (R := R) i ↔
      setup.attachmentCompatible
        (R.attach i)
        (setup.boundaryOf (R.packets i).state)
        (setup.glueBoundary
          (setup.boundaryOf (R.packets i).state)
          (R.packets i).refinedIn (R.packets i).refinedOut (R.attach i))
        (R.packets i).refinedIn (R.packets i).refinedOut = true :=
  Iff.rfl

/-! ### Boundary exposure under sink deletion

`def:boundary-exposure` (L1224), lifted to records. -/

/-- Boundary exposure under sink deletion, lifted from the carrier
operation `setup.exposeBoundaryUnderSinkDeletion` to a completed
reconstruction record.

Faithful to `def:boundary-exposure` (`our_paper_draft.tex` L1224):
given a sink packet `s` of a completed reconstruction record `R`, the
exposed boundary `Y_s` is obtained by removing the refined outputs of
`s` from the target boundary `Y` (step (i)) and exposing the unmatched
inputs of `s` produced by predecessors (step (ii)).

The `unmatchedInputs` argument records the refined inputs of `s` (per
step (ii)); the manuscript implicitly identifies these with the refined
inputs of `s` itself, since by C1 each one is matched by some predecessor's
output and the new boundary exposes those predecessor outputs. -/
def exposedBoundary
    {R : CompletedReconstructionRecord setup}
    (s : Fin R.n) : setup.BoundaryObject :=
  setup.exposeBoundaryUnderSinkDeletion R.Y
    (R.packets s).refinedOut (R.packets s).refinedIn

@[simp] theorem exposedBoundary_eq_exposeBoundaryUnderSinkDeletion
    {R : CompletedReconstructionRecord setup}
    (s : Fin R.n) :
    setup.exposedBoundary (R := R) s =
      setup.exposeBoundaryUnderSinkDeletion R.Y
        (R.packets s).refinedOut (R.packets s).refinedIn :=
  rfl

theorem exposedBoundary_uses_packet_interfaces
    {R : CompletedReconstructionRecord setup}
    (s : Fin R.n) :
    setup.exposedBoundary (R := R) s =
      setup.exposeBoundaryUnderSinkDeletion R.Y
        (R.packets s).refinedOut (R.packets s).refinedIn :=
  rfl

/-! ### Refined completedness using typed C2

`def:completed-reconstruction-record` C2 (L1128) — refined, replacing the
placeholder `True` C2 from `IsCompleted` (cycle 2) with the typed-interface
predicate above. The other three clauses are unchanged. -/

/-- Strengthened completedness predicate: identical to
`CompletedReconstructionRecord.IsCompleted` except that the C2 placeholder
is replaced by `IsCompatibleAttachmentForPacket`. Faithful to all four
manuscript C-clauses (L1126). -/
structure CompletedReconstructionRecord.IsCompletedRefined
    (R : CompletedReconstructionRecord setup) : Prop where
  /-- (C1) every refined input of a later packet is matched: see
  `IsCompleted.c1`. -/
  c1 :
    ∀ (j : Fin R.n) (r : setup.RefinedInterface),
      r ∈ R.ports.packetIn j →
      (r ∈ R.ports.externalIn) ∨
        (∃ i : Fin R.n, R.dep.edge i j = true ∧ r ∈ R.ports.packetOut i)
  /-- (C2) typed-interface compatibility of every attachment witness, per
  `def:completed-reconstruction-record` (L1128). -/
  c2 : ∀ (i : Fin R.n), setup.IsCompatibleAttachmentForPacket (R := R) i
  /-- (C3) tensor decomposition matches the WCC structure: see
  `IsCompleted.c3`. -/
  c3 :
    (∀ (B : Fin R.n → Prop), B ∈ R.tensor.blocks →
        ∃ (i₀ : Fin R.n), B i₀ ∧
          ∀ (j : Fin R.n), B j ↔ R.dep.WCC i₀ j) ∧
    (∀ (i : Fin R.n),
        ∃ (B : Fin R.n → Prop), B ∈ R.tensor.blocks ∧ B i)
  /-- (C4) canonical key extends the dependence partial order: see
  `IsCompleted.c4`. -/
  c4 :
    ∀ (i j : Fin R.n), R.dep.edge i j = true → R.key.pos i < R.key.pos j

theorem CompletedReconstructionRecord.IsCompletedRefined.inputs_matched
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup)) :
    ∀ (j : Fin R.n) (r : setup.RefinedInterface),
      r ∈ R.ports.packetIn j →
      (r ∈ R.ports.externalIn) ∨
        (∃ i : Fin R.n, R.dep.edge i j = true ∧ r ∈ R.ports.packetOut i) :=
  hR.c1

theorem CompletedReconstructionRecord.IsCompletedRefined.attachments_compatible
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup)) :
    ∀ (i : Fin R.n), setup.IsCompatibleAttachmentForPacket (R := R) i :=
  hR.c2

theorem CompletedReconstructionRecord.IsCompletedRefined.attachmentCompatibleForPacket
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup))
    (i : Fin R.n) :
    setup.IsCompatibleAttachmentForPacket (R := R) i :=
  hR.c2 i

theorem CompletedReconstructionRecord.IsCompletedRefined.tensor_blocks_match_wcc
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup)) :
    (∀ (B : Fin R.n → Prop), B ∈ R.tensor.blocks →
        ∃ (i₀ : Fin R.n), B i₀ ∧ ∀ (j : Fin R.n), B j ↔ R.dep.WCC i₀ j) ∧
      (∀ (i : Fin R.n), ∃ (B : Fin R.n → Prop), B ∈ R.tensor.blocks ∧ B i) :=
  hR.c3

theorem CompletedReconstructionRecord.IsCompletedRefined.key_extends_dependence
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup)) :
    ∀ (i j : Fin R.n), R.dep.edge i j = true → R.key.pos i < R.key.pos j :=
  hR.c4

@[ext] theorem CompletedReconstructionRecord.IsCompletedRefined.ext
    {R : CompletedReconstructionRecord setup}
    {h₁ h₂ : R.IsCompletedRefined (setup := setup)}
    (hc1 : h₁.c1 = h₂.c1)
    (hc2 : h₁.c2 = h₂.c2)
    (hc3 : h₁.c3 = h₂.c3)
    (hc4 : h₁.c4 = h₂.c4) :
    h₁ = h₂ := by
  cases h₁
  cases h₂
  cases hc1
  cases hc2
  cases hc3
  cases hc4
  rfl

/-! ### Direct c2/c4 accessor aliases for BoundaryTraceClass -/

/-- Direct C2 accessor: the attachment at index `i` is compatible (`Bool = true` form). -/
theorem CompletedReconstructionRecord.IsCompletedRefined.c2_at
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup))
    (i : Fin R.n) :
    setup.attachmentCompatible
      (R.attach i)
      (setup.boundaryOf (R.packets i).state)
      (setup.glueBoundary
        (setup.boundaryOf (R.packets i).state)
        (R.packets i).refinedIn (R.packets i).refinedOut (R.attach i))
      (R.packets i).refinedIn (R.packets i).refinedOut = true :=
  (isCompatibleAttachmentForPacket_eq_attachmentCompatible
    (setup := setup) (R := R) i).mp (hR.c2 i)

/-- Direct C4 accessor: the canonical key is strictly increasing along dependency edges. -/
theorem CompletedReconstructionRecord.IsCompletedRefined.c4_at
    {R : CompletedReconstructionRecord setup}
    (hR : R.IsCompletedRefined (setup := setup))
    {i j : Fin R.n} (h : R.dep.edge i j = true) :
    R.key.pos i < R.key.pos j :=
  hR.c4 i j h

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
