import TraceCalc.LayerB.RealObjects.SinkPeel

/-!
# Real-objects formalization: sink-deletion inverse / one-step unpeeling

**Phase 3B item 4 (2026-04-24).** This file constructs the one-step
inverse of `peelSink` (`SinkPeel.lean`, cycle 6 + Phase 3A item 2):

```
unpeelSink R' sinkData : CompletedReconstructionRecord setup
```

extends a completed-reconstruction-record `R'` of size `m` to a record
of size `m + 1` by reinserting a sink packet at a chosen position with
explicit boundary/key/tensor data carried in `SinkData`.

The inverse theorem (deliverable 7) takes the form

```
unpeelSink (peelSink R s) (sinkData R s) ≃ R
```

where `≃` is the *propositional* `RecordEquiv` predicate (field-wise
equality with `Fin.cast` reindexing where needed). Definitional equality
is too strong because `peelSink` re-`embedSkip`-indexes packets/ports/
attach and recomputes `Y`/`tensor`/`key`/`externalOut` from `R` and
`s` — the carried `SinkData` recovers those recomputed fields by
remembering the originals.

## Scope discipline (per user's verbatim Phase 3B item 4 spec)

* Does **not** prove `canonicalWord_replays`.
* Does **not** prove CanNF equality detection.
* Does **not** claim global reconstruction uniqueness beyond the
  already-proved order/word uniqueness in `PeelChain.lean`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the recursive
  descent inverted here.
* L1186–L1192 (the descent of `lem:sink-peel-preserves-completedness`),
  whose one-step inverse is the operation defined here.
* L1224 (`def:boundary-exposure`) — the boundary-recovery condition
  that motivates carrying `Y`/`externalOut` in `SinkData`.

## Namespace

Everything lives under `TraceCalc.LayerB.RealObjects`.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### `SinkData`: the data lost when peeling a sink

When we apply `peelSink R s`, we lose:
1. The sink packet `R.packets s` and its attach witness `R.attach s`,
2. The sink's refined input/output port lists,
3. The sink's incoming dependency edges (sinks have no outgoing edges,
   so only incoming need to be recorded),
4. The pre-peel boundary object `R.Y` and the pre-peel
   `R.ports.externalOut`,
5. The pre-peel tensor decomposition `R.tensor` and canonical key
   `R.key`.

The `SinkData R'` structure carries exactly this data, parameterized
by the *residual* record `R'` (the would-be result of peeling). The
position field `pos : Fin (R'.n + 1)` records where the sink sits in
the rebuilt record. -/

/-- The data needed to invert one step of `peelSink`: the sink position
in the rebuilt record, the sink packet and its attachment, the sink's
port lists, the sink's incoming dependency edges, and the pre-peel
boundary/tensor/key data that `peelSink` recomputes (and so loses). -/
structure SinkData (setup : RewriteCalculusSetup.{u})
    (R' : CompletedReconstructionRecord setup) where
  /-- Position of the sink in the rebuilt record's `Fin (R'.n + 1)`
  index space. -/
  pos : Fin (R'.n + 1)
  /-- The sink packet's data. -/
  packet : Packet setup
  /-- The sink's attachment / gluing witness. -/
  attach : setup.GluingWitness
  /-- The sink's refined input port list. -/
  packetIn : List setup.RefinedInterface
  /-- The sink's refined output port list. -/
  packetOut : List setup.RefinedInterface
  /-- Incoming dependency edges to the sink from each existing packet
  of `R'` (sinks have no outgoing edges, so outgoing data is omitted). -/
  incomingEdges : Fin R'.n → Bool
  /-- Pre-peel boundary object — lost when `peelSink` recomputes
  `restrictedY`. -/
  Y : setup.BoundaryObject
  /-- Pre-peel external-output list — lost when `peelSink` recomputes
  `restrictedExternalOut`. -/
  externalOut : List setup.RefinedInterface
  /-- Pre-peel tensor decomposition — lost when `peelSink` recomputes
  `restrictedTensor`. -/
  tensor : TensorDecomposition (R'.n + 1)
  /-- Pre-peel canonical key — lost when `peelSink` recomputes
  `restrictedKey`. -/
  key : CanonicalKey (R'.n + 1)

/-! ### Index-insertion inverse to `embedSkip`

For `pos : Fin (m + 1)`, we need a function `Fin (m + 1) → Option (Fin m)`
that inverts the embedding `embedSkip pos : Fin m → Fin (m + 1)`:
sends `pos` to `none` and any other index to its `embedSkip`-preimage.
We split into two helpers parallel to `predIndexLt`/`predIndexGt`. -/

/-- Reduce an index `i : Fin (m + 1)` distinct from `pos` to its
`embedSkip pos`-preimage in `Fin m`. -/
def reduceIdx {m : Nat} (pos : Fin (m + 1)) (i : Fin (m + 1))
    (hne : i ≠ pos) : Fin m :=
  if hlt : i.val < pos.val then
    predIndexLt pos i hlt
  else
    have hgt : pos.val < i.val := by
      rcases Nat.lt_or_ge pos.val i.val with h | h
      · exact h
      · exact absurd (Fin.ext (show i.val = pos.val by omega)) hne
    predIndexGt pos i hgt

/-- `embedSkip pos (reduceIdx pos i _) = i`. -/
lemma embedSkip_reduceIdx {m : Nat} (pos : Fin (m + 1)) (i : Fin (m + 1))
    (hne : i ≠ pos) :
    embedSkip pos (reduceIdx pos i hne) = i := by
  unfold reduceIdx
  by_cases hlt : i.val < pos.val
  · simp [hlt, embedSkip_predIndexLt]
  · have hgt : pos.val < i.val := by
      rcases Nat.lt_or_ge pos.val i.val with h | h
      · exact h
      · exact absurd (Fin.ext (show i.val = pos.val by omega)) hne
    simp [hlt, embedSkip_predIndexGt]

/-- `reduceIdx pos (embedSkip pos j) _ = j`. -/
lemma reduceIdx_embedSkip {m : Nat} (pos : Fin (m + 1)) (j : Fin m) :
    reduceIdx pos (embedSkip pos j) (embedSkip_ne pos j) = j := by
  apply embedSkip_injective pos
  rw [embedSkip_reduceIdx]

/-! ### `unpeelSink`: the one-step extension operation -/

/-- The dependency-edge function of the rebuilt record. The sink (at
`pos`) has no outgoing edges; incoming edges to it come from
`sd.incomingEdges`; all other edges come from `R'.dep` (with both
endpoints reduced through `reduceIdx pos`). -/
def unpeelEdge {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') (i j : Fin (R'.n + 1)) : Bool :=
  if hi : i = sd.pos then false
  else if hj : j = sd.pos then sd.incomingEdges (reduceIdx sd.pos i hi)
  else R'.dep.edge (reduceIdx sd.pos i hi) (reduceIdx sd.pos j hj)

/-- Every step `unpeelEdge sd a b = true` has source `a ≠ sd.pos`,
because `unpeelEdge sd pos _ = false` by construction. -/
private lemma unpeelEdge_src_ne_pos {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') {a b : Fin (R'.n + 1)}
    (h : unpeelEdge sd a b = true) : a ≠ sd.pos := by
  intro ha
  rw [unpeelEdge, dif_pos ha] at h
  exact Bool.false_ne_true h

/-- The head of any `TransGen unpeelEdge` chain has source ≠ `sd.pos`. -/
private lemma transGen_unpeelEdge_head_ne_pos
    {R' : CompletedReconstructionRecord setup} (sd : SinkData setup R')
    {a b : Fin (R'.n + 1)}
    (h : Relation.TransGen
        (fun a b : Fin (R'.n + 1) => unpeelEdge sd a b = true) a b) :
    a ≠ sd.pos := by
  induction h with
  | single h' => exact unpeelEdge_src_ne_pos sd h'
  | tail _ _ ih => exact ih

/-- Project a `TransGen unpeelEdge` chain to a `TransGen R'.dep.edge`
chain when both endpoints avoid `sd.pos`. (Intermediate vertices also
avoid `sd.pos` because they appear as sources of subsequent steps.) -/
private lemma transGen_unpeelEdge_project
    {R' : CompletedReconstructionRecord setup} (sd : SinkData setup R')
    {a b : Fin (R'.n + 1)}
    (h : Relation.TransGen
        (fun a b : Fin (R'.n + 1) => unpeelEdge sd a b = true) a b)
    (ha : a ≠ sd.pos) (hb : b ≠ sd.pos) :
    Relation.TransGen
      (fun a b : Fin R'.n => R'.dep.edge a b = true)
      (reduceIdx sd.pos a ha) (reduceIdx sd.pos b hb) := by
  induction h with
  | @single b hab =>
    apply Relation.TransGen.single
    rw [unpeelEdge, dif_neg ha, dif_neg hb] at hab
    exact hab
  | @tail b' c hbc' hc' ih =>
    have hb' : b' ≠ sd.pos := unpeelEdge_src_ne_pos sd hc'
    refine Relation.TransGen.tail (ih hb') ?_
    rw [unpeelEdge, dif_neg hb', dif_neg hb] at hc'
    exact hc'

/-- The dependency DAG of the rebuilt record. Acyclicity follows
because (a) the sink has no outgoing edges, so no cycle's source can
be `pos`; and (b) cycles `k →+ k` with `k ≠ pos` project to cycles
in `R'.dep`, contradiction. -/
def unpeelDep {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') : DepGraph (R'.n + 1) where
  edge := unpeelEdge sd
  acyclic := by
    intro k hcycle
    have hk_ne : k ≠ sd.pos :=
      transGen_unpeelEdge_head_ne_pos sd hcycle
    have hchain := transGen_unpeelEdge_project sd hcycle hk_ne hk_ne
    exact R'.dep.acyclic _ hchain

/-- The packet function of the rebuilt record. -/
def unpeelPackets {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') (i : Fin (R'.n + 1)) : Packet setup :=
  if h : i = sd.pos then sd.packet
  else R'.packets (reduceIdx sd.pos i h)

/-- The attach function of the rebuilt record. -/
def unpeelAttach {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') (i : Fin (R'.n + 1)) : setup.GluingWitness :=
  if h : i = sd.pos then sd.attach
  else R'.attach (reduceIdx sd.pos i h)

/-- The per-packet refined-input list of the rebuilt record. -/
def unpeelPacketIn {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') (i : Fin (R'.n + 1)) :
    List setup.RefinedInterface :=
  if h : i = sd.pos then sd.packetIn
  else R'.ports.packetIn (reduceIdx sd.pos i h)

/-- The per-packet refined-output list of the rebuilt record. -/
def unpeelPacketOut {R' : CompletedReconstructionRecord setup}
    (sd : SinkData setup R') (i : Fin (R'.n + 1)) :
    List setup.RefinedInterface :=
  if h : i = sd.pos then sd.packetOut
  else R'.ports.packetOut (reduceIdx sd.pos i h)

/-- **Deliverable 1: the one-step reattachment operation.**

`unpeelSink R' sd` extends `R'` to a record of size `R'.n + 1` by
inserting a sink packet at `sd.pos` with the data carried by `sd`. -/
def unpeelSink (R' : CompletedReconstructionRecord setup)
    (sd : SinkData setup R') : CompletedReconstructionRecord setup where
  n := R'.n + 1
  X := R'.X
  Y := sd.Y
  ports :=
    { externalIn := R'.ports.externalIn
      externalOut := sd.externalOut
      packetIn := unpeelPacketIn sd
      packetOut := unpeelPacketOut sd }
  packets := unpeelPackets sd
  dep := unpeelDep sd
  attach := unpeelAttach sd
  tensor := sd.tensor
  key := sd.key

/-! ### Restoration theorems (deliverables 2–6) -/

/-- **Deliverable 2: packet-count restoration.** -/
@[simp] theorem unpeelSink_n
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).n = R'.n + 1 := rfl

/-- **Deliverable 3: dependency restoration (sink edge profile).** The
sink at `sd.pos` has no outgoing edges. -/
@[simp] theorem unpeelSink_dep_no_outgoing
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R')
    (j : Fin (R'.n + 1)) :
    (unpeelSink R' sd).dep.edge sd.pos j = false := by
  show unpeelEdge sd sd.pos j = false
  unfold unpeelEdge
  rw [dif_pos rfl]

/-- **Deliverable 3 (continued).** Incoming edges to the sink from
existing packets are exactly `sd.incomingEdges` (after reduction). -/
theorem unpeelSink_dep_incoming
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R')
    (i : Fin (R'.n + 1)) (hi : i ≠ sd.pos) :
    (unpeelSink R' sd).dep.edge i sd.pos
      = sd.incomingEdges (reduceIdx sd.pos i hi) := by
  show unpeelEdge sd i sd.pos = _
  unfold unpeelEdge
  rw [dif_neg hi, dif_pos rfl]

/-- **Deliverable 3 (continued).** Edges between two existing
(non-sink) packets agree with `R'.dep` (after reduction). -/
theorem unpeelSink_dep_existing
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R')
    (i j : Fin (R'.n + 1)) (hi : i ≠ sd.pos) (hj : j ≠ sd.pos) :
    (unpeelSink R' sd).dep.edge i j
      = R'.dep.edge (reduceIdx sd.pos i hi) (reduceIdx sd.pos j hj) := by
  show unpeelEdge sd i j = _
  unfold unpeelEdge
  rw [dif_neg hi, dif_neg hj]

/-- **Deliverable 4: boundary restoration (target).** -/
@[simp] theorem unpeelSink_Y
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).Y = sd.Y := rfl

/-- **Deliverable 4 (continued): external-output restoration.** -/
@[simp] theorem unpeelSink_externalOut
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).ports.externalOut = sd.externalOut := rfl

/-- **Deliverable 4 (continued): source-boundary restoration.** -/
@[simp] theorem unpeelSink_X
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).X = R'.X := rfl

/-- **Deliverable 4 (continued): external-input restoration.** -/
@[simp] theorem unpeelSink_externalIn
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).ports.externalIn = R'.ports.externalIn := rfl

/-- **Deliverable 5: tensor restoration.** -/
@[simp] theorem unpeelSink_tensor
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).tensor = sd.tensor := rfl

/-- **Deliverable 6: key restoration.** -/
@[simp] theorem unpeelSink_key
    (R' : CompletedReconstructionRecord setup) (sd : SinkData setup R') :
    (unpeelSink R' sd).key = sd.key := rfl

/-! ### `sinkData`: the data extracted from a record at a sink

The companion to `unpeelSink`: given a record `R` and a sink position
`s : Fin R.n`, package up the data needed to rebuild `R` from
`peelSink R s`. -/

/-- The position `s` of `R.n`-typed indexing recast to position
in the residual + 1 indexing. Uses `R.n - 1 + 1 = R.n` (valid since
`Fin R.n` is inhabited by `s`). -/
def sinkPosCast (R : CompletedReconstructionRecord setup) (s : Fin R.n) :
    Fin ((peelSink R s).n + 1) :=
  ⟨s.val, by
    show s.val < R.n - 1 + 1
    have := s.isLt
    omega⟩

/-- **Companion to `unpeelSink`.** Extract from `R` and a sink `s` the
`SinkData` needed to invert `peelSink R s`. -/
def sinkData (R : CompletedReconstructionRecord setup) (s : Fin R.n) :
    SinkData setup (peelSink R s) where
  pos := sinkPosCast R s
  packet := R.packets s
  attach := R.attach s
  packetIn := R.ports.packetIn s
  packetOut := R.ports.packetOut s
  incomingEdges := fun i => R.dep.edge (embedSkip s i) s
  Y := R.Y
  externalOut := R.ports.externalOut
  tensor := by
    -- `R.tensor : TensorDecomposition R.n`; we need
    -- `TensorDecomposition ((peelSink R s).n + 1)`. Since
    -- `(peelSink R s).n + 1 = R.n - 1 + 1 = R.n`, cast.
    have hn : (peelSink R s).n + 1 = R.n := by
      show R.n - 1 + 1 = R.n
      have := s.isLt; omega
    exact hn ▸ R.tensor
  key := by
    have hn : (peelSink R s).n + 1 = R.n := by
      show R.n - 1 + 1 = R.n
      have := s.isLt; omega
    exact hn ▸ R.key

/-- The crucial value-level identity: for any `i` distinct from
`(sinkData R s).pos`, the round-trip
`embedSkip s ∘ reduceIdx (sinkData R s).pos` preserves `.val`.

This is needed because the rewrite lemma `embedSkip_reduceIdx`
requires both `pos` arguments to be the same Lean term, but in our
inverse-theorem proof obligation the `embedSkip` uses
`s : Fin R.n` while `reduceIdx` uses
`(sinkData R s).pos : Fin ((peelSink R s).n + 1)` — they have equal
values but live in different `Fin` types. -/
private lemma embedSkip_s_reduceIdx_pos_val
    (R : CompletedReconstructionRecord setup) (s : Fin R.n)
    (i : Fin ((peelSink R s).n + 1)) (hi : i ≠ (sinkData R s).pos) :
    (embedSkip s (reduceIdx (sinkData R s).pos i hi)).val = i.val := by
  have hposval : ((sinkData R s).pos).val = s.val := rfl
  unfold reduceIdx
  by_cases hlt : i.val < (sinkData R s).pos.val
  · rw [dif_pos hlt]
    have hlt' : (predIndexLt (sinkData R s).pos i hlt).val < s.val := by
      show i.val < s.val
      rw [← hposval]; exact hlt
    rw [embedSkip_lt s _ hlt']
    rfl
  · rw [dif_neg hlt]
    have hgt : (sinkData R s).pos.val < i.val := by
      rcases Nat.lt_or_ge (sinkData R s).pos.val i.val with h | h
      · exact h
      · exact absurd (Fin.ext (show i.val = (sinkData R s).pos.val by omega)) hi
    have hge : ¬ ((predIndexGt (sinkData R s).pos i hgt).val < s.val) := by
      show ¬ (i.val - 1 < s.val)
      rw [← hposval]; omega
    rw [embedSkip_ge s _ hge]
    show i.val - 1 + 1 = i.val
    omega

/-! ### Propositional record equivalence (`RecordEquiv`)

Two completed reconstruction records over the same `setup` are
*propositionally equivalent* when they have equal packet counts and
all eight components agree pointwise (with the index cast given by the
common packet count). -/

/-- Propositional equivalence of two `CompletedReconstructionRecord`s
over the same `setup`. Field-by-field equality with `Fin.cast` for
index reindexing. -/
structure RecordEquiv (R₁ R₂ : CompletedReconstructionRecord setup) :
    Prop where
  /-- Packet counts agree. -/
  n_eq : R₁.n = R₂.n
  /-- Source boundaries agree. -/
  X_eq : R₁.X = R₂.X
  /-- Target boundaries agree. -/
  Y_eq : R₁.Y = R₂.Y
  /-- External-input lists agree. -/
  externalIn_eq : R₁.ports.externalIn = R₂.ports.externalIn
  /-- External-output lists agree. -/
  externalOut_eq : R₁.ports.externalOut = R₂.ports.externalOut
  /-- Per-packet input ports agree pointwise (with index recast). -/
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

/-! ### Deliverable 7: the one-step inverse theorem

`unpeelSink (peelSink R s) (sinkData R s) ≃ R`.

Proof strategy: discharge each conjunct of `RecordEquiv` field-by-field.
The packet-count conjunct unfolds via `(peelSink R s).n + 1 = R.n - 1 + 1 = R.n`
(`Nat.sub_add_cancel` from `0 < R.n`). The pointwise conjuncts split
on `i = sd.pos` vs `i ≠ sd.pos`, with the equal branch resolved by
`Fin.cast` of `s` and the unequal branch resolved by
`embedSkip_reduceIdx`. -/

/-- **Deliverable 7: one-step inverse theorem (propositional form).**
`unpeelSink (peelSink R s) (sinkData R s)` is `RecordEquiv` to `R`,
provided `s` is a sink of `R`. The sink hypothesis is needed only for
the `dep_edge_eq` field at indices `i = sd.pos`, where the unpeeled
record reports `false` and we must match it against `R.dep.edge s _`. -/
theorem unpeelSink_peelSink (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) (hSink : R.IsSink s) :
    RecordEquiv (unpeelSink (peelSink R s) (sinkData R s)) R := by
  have hpos : 0 < R.n := by have := s.isLt; omega
  have hn_eq : (unpeelSink (peelSink R s) (sinkData R s)).n = R.n := by
    show (peelSink R s).n + 1 = R.n
    show R.n - 1 + 1 = R.n
    omega
  refine
    { n_eq := hn_eq
      X_eq := ?_
      Y_eq := ?_
      externalIn_eq := ?_
      externalOut_eq := ?_
      packetIn_eq := ?_
      packetOut_eq := ?_
      packets_eq := ?_
      dep_edge_eq := ?_
      attach_eq := ?_ }
  · -- X_eq
    show (peelSink R s).X = R.X
    rfl
  · -- Y_eq
    show (sinkData R s).Y = R.Y
    rfl
  · -- externalIn_eq
    show (peelSink R s).ports.externalIn = R.ports.externalIn
    rfl
  · -- externalOut_eq
    show (sinkData R s).externalOut = R.ports.externalOut
    rfl
  · -- packetIn_eq
    intro i
    show unpeelPacketIn (sinkData R s) i = R.ports.packetIn (Fin.cast hn_eq i)
    unfold unpeelPacketIn
    by_cases hi : i = (sinkData R s).pos
    · rw [dif_pos hi]
      show R.ports.packetIn s = R.ports.packetIn (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      have : i.val = s.val := congrArg Fin.val hi
      simp [Fin.cast, this]
    · rw [dif_neg hi]
      show (peelSink R s).ports.packetIn (reduceIdx _ i hi)
          = R.ports.packetIn (Fin.cast hn_eq i)
      show R.ports.packetIn (embedSkip s (reduceIdx _ i hi))
          = R.ports.packetIn (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      rw [embedSkip_s_reduceIdx_pos_val R s i hi]
      simp [Fin.cast]
  · -- packetOut_eq
    intro i
    show unpeelPacketOut (sinkData R s) i
        = R.ports.packetOut (Fin.cast hn_eq i)
    unfold unpeelPacketOut
    by_cases hi : i = (sinkData R s).pos
    · rw [dif_pos hi]
      show R.ports.packetOut s = R.ports.packetOut (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      have : i.val = s.val := congrArg Fin.val hi
      simp [Fin.cast, this]
    · rw [dif_neg hi]
      show (peelSink R s).ports.packetOut (reduceIdx _ i hi)
          = R.ports.packetOut (Fin.cast hn_eq i)
      show R.ports.packetOut (embedSkip s (reduceIdx _ i hi))
          = R.ports.packetOut (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      rw [embedSkip_s_reduceIdx_pos_val R s i hi]
      simp [Fin.cast]
  · -- packets_eq
    intro i
    show unpeelPackets (sinkData R s) i = R.packets (Fin.cast hn_eq i)
    unfold unpeelPackets
    by_cases hi : i = (sinkData R s).pos
    · rw [dif_pos hi]
      show R.packets s = R.packets (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      have : i.val = s.val := congrArg Fin.val hi
      simp [Fin.cast, this]
    · rw [dif_neg hi]
      show (peelSink R s).packets (reduceIdx _ i hi)
          = R.packets (Fin.cast hn_eq i)
      show R.packets (embedSkip s (reduceIdx _ i hi))
          = R.packets (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      rw [embedSkip_s_reduceIdx_pos_val R s i hi]
      simp [Fin.cast]
  · -- dep_edge_eq
    intro i j
    show (unpeelSink (peelSink R s) (sinkData R s)).dep.edge i j
        = R.dep.edge (Fin.cast hn_eq i) (Fin.cast hn_eq j)
    show unpeelEdge (sinkData R s) i j
        = R.dep.edge (Fin.cast hn_eq i) (Fin.cast hn_eq j)
    unfold unpeelEdge
    by_cases hi : i = (sinkData R s).pos
    · rw [dif_pos hi]
      have hi_val : i.val = s.val := congrArg Fin.val hi
      have hcast_i : Fin.cast hn_eq i = s := by
        apply Fin.ext; simp [Fin.cast, hi_val]
      rw [hcast_i]
      symm
      exact hSink (Fin.cast hn_eq j)
    · rw [dif_neg hi]
      by_cases hj : j = (sinkData R s).pos
      · rw [dif_pos hj]
        show R.dep.edge (embedSkip s (reduceIdx _ i hi)) s
            = R.dep.edge (Fin.cast hn_eq i) (Fin.cast hn_eq j)
        congr 1
        · apply Fin.ext
          rw [embedSkip_s_reduceIdx_pos_val R s i hi]
          simp [Fin.cast]
        · apply Fin.ext
          have : j.val = s.val := congrArg Fin.val hj
          simp [Fin.cast, this]
      · rw [dif_neg hj]
        show (peelSink R s).dep.edge (reduceIdx _ i hi) (reduceIdx _ j hj)
            = R.dep.edge (Fin.cast hn_eq i) (Fin.cast hn_eq j)
        show R.dep.edge (embedSkip s (reduceIdx _ i hi))
              (embedSkip s (reduceIdx _ j hj))
            = R.dep.edge (Fin.cast hn_eq i) (Fin.cast hn_eq j)
        congr 1
        · apply Fin.ext
          rw [embedSkip_s_reduceIdx_pos_val R s i hi]
          simp [Fin.cast]
        · apply Fin.ext
          rw [embedSkip_s_reduceIdx_pos_val R s j hj]
          simp [Fin.cast]
  · -- attach_eq
    intro i
    show unpeelAttach (sinkData R s) i = R.attach (Fin.cast hn_eq i)
    unfold unpeelAttach
    by_cases hi : i = (sinkData R s).pos
    · rw [dif_pos hi]
      show R.attach s = R.attach (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      have : i.val = s.val := congrArg Fin.val hi
      simp [Fin.cast, this]
    · rw [dif_neg hi]
      show (peelSink R s).attach (reduceIdx _ i hi)
          = R.attach (Fin.cast hn_eq i)
      show R.attach (embedSkip s (reduceIdx _ i hi))
          = R.attach (Fin.cast hn_eq i)
      congr 1
      apply Fin.ext
      rw [embedSkip_s_reduceIdx_pos_val R s i hi]
      simp [Fin.cast]

/-
TEX ref: our_paper_draft.tex, label lem:sink-deletion-inverse (L1160+)
Paper role: peeling a sink and then unpeeling is the identity up to RecordEquiv;
  the sink-peel operation is invertible via unpeelSink
Lean status: PROVED → named alias added (M0/M2)
-/
/-- **`lem:sink-deletion-inverse`** (manuscript alias): peeling a sink from `R`
and then unpeeling the result is record-equivalent to `R`.

This is a named alias for `unpeelSink_peelSink`, which already provides the
full proof. The name `sink_deletion_inverse` matches the manuscript lemma label. -/
theorem sink_deletion_inverse
    {setup : RewriteCalculusSetup.{u}}
    (R : CompletedReconstructionRecord setup) (s : Fin R.n)
    (hSink : R.IsSink s) :
    RecordEquiv (unpeelSink (peelSink R s) (sinkData R s)) R :=
  unpeelSink_peelSink R s hSink

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
