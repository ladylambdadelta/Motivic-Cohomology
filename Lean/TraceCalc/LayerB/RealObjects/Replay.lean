import TraceCalc.LayerB.RealObjects.UnpeelChain

/-!
# Real-objects formalization: terminal-to-root peel-chain replay interpreter

Lean status: PROVED; immediate consequence of replay_stable
replay interpreter** missing from `UnpeelChain.lean` (Phase 3B item 5a):
a `PeelChain.replay` whose `cons` case **consumes** the tail's
reconstruction, in contrast to the prefix-local
`PeelChain.reconstruct` whose `cons` case ignored `tail`.

```
replay : ∀ {R}, PeelChain R → CompletedReconstructionRecord setup
replay (nil R _) := R
Lean status: PROVED; direct corollary of replay_recordEquiv
                                       (sinkData R s |>.castN ...)
```

**Per user's verbatim Phase 3B item 5b directive**: keep
`reconstruct` / `reconstruct_recordEquiv` as the local/prefix theorem;
add this as a separate, stronger replay definition.

## Architecture

* `SinkData.castN` — transport `SinkData` along an `n`-equality. Only
  the `R'`-dependent fields (`pos : Fin (R'.n + 1)`,
  `incomingEdges : Fin R'.n → Bool`,
  `tensor : TensorDecomposition (R'.n + 1)`,
  `key : CanonicalKey (R'.n + 1)`) need transport; the rest are
  `R'`-independent.
* `unpeelSink_castN_recordEquiv` — the congruence lemma. If
  `R₁ ≃ R₂` and `sd₂ : SinkData R₂`, then unpeeling `sd₂` over `R₂`
  is `RecordEquiv` to unpeeling its `castN`-transport over `R₁`.
* `PeelChain.replayAux` — Σ-bundled structural recursion producing
  `{r // r.n = R.n}`; the size-equality witness is propagated
  alongside the record so the cons case can transport `sinkData R s`.
* `PeelChain.replay` — projection of `replayAux`.
* `PeelChain.replay_recordEquiv` — headline: `RecordEquiv (replay c) R`,
  proved by structural induction on `c`, using the IH on `tail` to
  apply `unpeelSink_castN_recordEquiv` and chaining with
  `unpeelSink_peelSink` from `Unpeel.lean`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the recursive
  descent whose **terminal-to-root** reverse direction is here.
* L1186–L1192 — the per-step descent run in reverse, terminal residue
  to root.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### Transport `SinkData` along an `n`-equality -/

namespace SinkData

/-- Transport a `SinkData R₁` along `R₁.n = R₂.n` to a `SinkData R₂`.
The four `R'`-dependent fields (`pos`, `incomingEdges`, `tensor`,
`key`) are recast through `Fin.cast` / dependent rewriting; the
`R'`-independent fields (`packet`, `attach`, `packetIn`, `packetOut`,
`Y`, `externalOut`) are preserved verbatim. -/
def castN {R₁ R₂ : CompletedReconstructionRecord setup}
    (sd : SinkData setup R₁) (h : R₁.n = R₂.n) : SinkData setup R₂ where
  pos := Fin.cast (by rw [h]) sd.pos
  packet := sd.packet
  attach := sd.attach
  packetIn := sd.packetIn
  packetOut := sd.packetOut
  incomingEdges := fun i => sd.incomingEdges (Fin.cast h.symm i)
  Y := sd.Y
  externalOut := sd.externalOut
  tensor := h ▸ sd.tensor
  key := h ▸ sd.key

/-- `castN` along `rfl` is the identity. -/
@[simp] theorem castN_rfl {R : CompletedReconstructionRecord setup}
    (sd : SinkData setup R) :
    sd.castN (rfl : R.n = R.n) = sd := by
  cases sd; rfl

end SinkData

/-! ### Congruence of `unpeelSink` along `RecordEquiv` -/

/-- **Key congruence lemma.** If `R₁ ≃ R₂` (as `RecordEquiv`) and
`sd₂` is `SinkData` over `R₂`, then unpeeling `sd₂` over `R₂` is
`RecordEquiv` to unpeeling its `castN`-transport over `R₁`.

This is the bridge missing from `UnpeelChain.lean`: it lets a peel-chain
replay interpreter consume a tail result that is only **propositionally**
equal (via `RecordEquiv`) to the exact peeled record `peelSink R s`,
not definitionally so. -/
theorem unpeelSink_castN_recordEquiv
    {R₁ R₂ : CompletedReconstructionRecord setup}
    (h : RecordEquiv R₁ R₂) (sd₂ : SinkData setup R₂) :
    RecordEquiv (unpeelSink R₁ (sd₂.castN h.n_eq.symm)) (unpeelSink R₂ sd₂) := by
  -- A `Fin.cast` collapse that recurs throughout the proof:
  -- (sd₂.castN h.n_eq.symm).pos = Fin.cast (by rw [h.n_eq.symm]) sd₂.pos
  -- has `.val = sd₂.pos.val`.
  have hposval :
      ((sd₂.castN h.n_eq.symm).pos).val = sd₂.pos.val := rfl
  have hn_unp : (unpeelSink R₁ (sd₂.castN h.n_eq.symm)).n
      = (unpeelSink R₂ sd₂).n := by
    show R₁.n + 1 = R₂.n + 1
    rw [h.n_eq]
  -- A reusable index-equivalence: `i ≠ pos₁` iff `cast i ≠ pos₂`.
  refine
    { n_eq := hn_unp
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
    show R₁.X = R₂.X; exact h.X_eq
  · -- Y_eq
    show (sd₂.castN h.n_eq.symm).Y = sd₂.Y; rfl
  · -- externalIn_eq
    show R₁.ports.externalIn = R₂.ports.externalIn; exact h.externalIn_eq
  · -- externalOut_eq
    show (sd₂.castN h.n_eq.symm).externalOut = sd₂.externalOut; rfl
  · -- packetIn_eq
    intro i
    show unpeelPacketIn (sd₂.castN h.n_eq.symm) i
        = unpeelPacketIn sd₂ (Fin.cast hn_unp i)
    unfold unpeelPacketIn
    by_cases hi : i = (sd₂.castN h.n_eq.symm).pos
    · rw [dif_pos hi]
      have hi_cast : Fin.cast hn_unp i = sd₂.pos := by
        apply Fin.ext
        have : i.val = sd₂.pos.val := by
          have := congrArg Fin.val hi
          simp [hposval] at this; exact this
        simp [Fin.cast, this]
      rw [dif_pos hi_cast]
      rfl
    · rw [dif_neg hi]
      have hi_cast_ne : Fin.cast hn_unp i ≠ sd₂.pos := by
        intro hcast
        apply hi
        apply Fin.ext
        have := congrArg Fin.val hcast
        simp [Fin.cast, hposval] at this ⊢
        exact this
      rw [dif_neg hi_cast_ne]
      have hred_val :
          (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)).val
            = (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne).val := by
        unfold reduceIdx
        by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
        · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
            simp [Fin.cast]; rw [← hposval]; exact hlt
          rw [dif_pos hlt, dif_pos hlt']; rfl
        · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
            intro hh; apply hlt
            simp [Fin.cast] at hh; rw [hposval]; exact hh
          rw [dif_neg hlt, dif_neg hlt']; rfl
      have hh := h.packetIn_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)
      rw [hh]
      congr 1
      apply Fin.ext; exact hred_val
  · -- packetOut_eq
    intro i
    show unpeelPacketOut (sd₂.castN h.n_eq.symm) i
        = unpeelPacketOut sd₂ (Fin.cast hn_unp i)
    unfold unpeelPacketOut
    by_cases hi : i = (sd₂.castN h.n_eq.symm).pos
    · rw [dif_pos hi]
      have hi_cast : Fin.cast hn_unp i = sd₂.pos := by
        apply Fin.ext
        have : i.val = sd₂.pos.val := by
          have := congrArg Fin.val hi; simp [hposval] at this; exact this
        simp [Fin.cast, this]
      rw [dif_pos hi_cast]
      rfl
    · rw [dif_neg hi]
      have hi_cast_ne : Fin.cast hn_unp i ≠ sd₂.pos := by
        intro hcast; apply hi; apply Fin.ext
        have := congrArg Fin.val hcast
        simp [Fin.cast, hposval] at this ⊢; exact this
      rw [dif_neg hi_cast_ne]
      have hred_val :
          (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)).val
            = (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne).val := by
        unfold reduceIdx
        by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
        · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
            simp [Fin.cast]; rw [← hposval]; exact hlt
          rw [dif_pos hlt, dif_pos hlt']; rfl
        · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
            intro hh; apply hlt
            simp [Fin.cast] at hh; rw [hposval]; exact hh
          rw [dif_neg hlt, dif_neg hlt']; rfl
      have hh := h.packetOut_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)
      rw [hh]
      congr 1
      apply Fin.ext; exact hred_val
  · -- packets_eq
    intro i
    show unpeelPackets (sd₂.castN h.n_eq.symm) i
        = unpeelPackets sd₂ (Fin.cast hn_unp i)
    unfold unpeelPackets
    by_cases hi : i = (sd₂.castN h.n_eq.symm).pos
    · rw [dif_pos hi]
      have hi_cast : Fin.cast hn_unp i = sd₂.pos := by
        apply Fin.ext
        have : i.val = sd₂.pos.val := by
          have := congrArg Fin.val hi; simp [hposval] at this; exact this
        simp [Fin.cast, this]
      rw [dif_pos hi_cast]
      rfl
    · rw [dif_neg hi]
      have hi_cast_ne : Fin.cast hn_unp i ≠ sd₂.pos := by
        intro hcast; apply hi; apply Fin.ext
        have := congrArg Fin.val hcast
        simp [Fin.cast, hposval] at this ⊢; exact this
      rw [dif_neg hi_cast_ne]
      -- Goal: R₁.packets (reduceIdx _ i hi)
      --     = R₂.packets (reduceIdx sd₂.pos (Fin.cast hn_unp i) _)
      -- Use h.packets_eq to bridge R₁.packets and R₂.packets, with
      -- the index-cast equation forcing the two `reduceIdx`s to align.
      have hred_val :
          (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)).val
            = (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne).val := by
        -- Both reduceIdx values are determined by their `i.val` and `pos.val`,
        -- and since both ambient pos.val and i.val agree across the cast,
        -- the two reduceIdx values agree.
        unfold reduceIdx
        by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
        · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
            simp [Fin.cast]; rw [← hposval]; exact hlt
          rw [dif_pos hlt, dif_pos hlt']
          rfl
        · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
            intro hh
            apply hlt
            simp [Fin.cast] at hh; rw [hposval]; exact hh
          rw [dif_neg hlt, dif_neg hlt']
          rfl
      have hh := h.packets_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)
      rw [hh]
      congr 1
      apply Fin.ext; exact hred_val
  · -- dep_edge_eq
    intro i j
    show (unpeelSink R₁ (sd₂.castN h.n_eq.symm)).dep.edge i j
        = (unpeelSink R₂ sd₂).dep.edge (Fin.cast hn_unp i) (Fin.cast hn_unp j)
    show unpeelEdge (sd₂.castN h.n_eq.symm) i j
        = unpeelEdge sd₂ (Fin.cast hn_unp i) (Fin.cast hn_unp j)
    unfold unpeelEdge
    by_cases hi : i = (sd₂.castN h.n_eq.symm).pos
    · have hi_cast : Fin.cast hn_unp i = sd₂.pos := by
        apply Fin.ext
        have : i.val = sd₂.pos.val := by
          have := congrArg Fin.val hi; simp [hposval] at this; exact this
        simp [Fin.cast, this]
      rw [dif_pos hi, dif_pos hi_cast]
    · have hi_cast_ne : Fin.cast hn_unp i ≠ sd₂.pos := by
        intro hcast; apply hi; apply Fin.ext
        have := congrArg Fin.val hcast
        simp [Fin.cast, hposval] at this ⊢; exact this
      rw [dif_neg hi, dif_neg hi_cast_ne]
      by_cases hj : j = (sd₂.castN h.n_eq.symm).pos
      · have hj_cast : Fin.cast hn_unp j = sd₂.pos := by
          apply Fin.ext
          have : j.val = sd₂.pos.val := by
            have := congrArg Fin.val hj; simp [hposval] at this; exact this
          simp [Fin.cast, this]
        rw [dif_pos hj, dif_pos hj_cast]
        -- Both branches return sd.incomingEdges at the reduced index.
        -- LHS: (sd₂.castN h.n_eq.symm).incomingEdges (reduceIdx _ i hi)
        --    = sd₂.incomingEdges (Fin.cast h.n_eq (reduceIdx ...))
        -- RHS: sd₂.incomingEdges (reduceIdx sd₂.pos (Fin.cast hn_unp i) _)
        show sd₂.incomingEdges
              (Fin.cast h.n_eq (reduceIdx _ i hi))
            = sd₂.incomingEdges (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne)
        congr 1
        apply Fin.ext
        unfold reduceIdx
        by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
        · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
            simp [Fin.cast]; rw [← hposval]; exact hlt
          rw [dif_pos hlt, dif_pos hlt']
          rfl
        · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
            intro hh; apply hlt
            simp [Fin.cast] at hh; rw [hposval]; exact hh
          rw [dif_neg hlt, dif_neg hlt']
          rfl
      · have hj_cast_ne : Fin.cast hn_unp j ≠ sd₂.pos := by
          intro hcast; apply hj; apply Fin.ext
          have := congrArg Fin.val hcast
          simp [Fin.cast, hposval] at this ⊢; exact this
        rw [dif_neg hj, dif_neg hj_cast_ne]
        -- Both branches return R.dep.edge at reduced indices; bridge via h.dep_edge_eq.
        have hred_i_val :
            (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)).val
              = (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne).val := by
          unfold reduceIdx
          by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
          · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
              simp [Fin.cast]; rw [← hposval]; exact hlt
            rw [dif_pos hlt, dif_pos hlt']; rfl
          · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
              intro hh; apply hlt
              simp [Fin.cast] at hh; rw [hposval]; exact hh
            rw [dif_neg hlt, dif_neg hlt']; rfl
        have hred_j_val :
            (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos j hj)).val
              = (reduceIdx sd₂.pos (Fin.cast hn_unp j) hj_cast_ne).val := by
          unfold reduceIdx
          by_cases hlt : j.val < ((sd₂.castN h.n_eq.symm).pos).val
          · have hlt' : (Fin.cast hn_unp j).val < sd₂.pos.val := by
              simp [Fin.cast]; rw [← hposval]; exact hlt
            rw [dif_pos hlt, dif_pos hlt']; rfl
          · have hlt' : ¬ ((Fin.cast hn_unp j).val < sd₂.pos.val) := by
              intro hh; apply hlt
              simp [Fin.cast] at hh; rw [hposval]; exact hh
            rw [dif_neg hlt, dif_neg hlt']; rfl
        have hh := h.dep_edge_eq
                  (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)
                  (reduceIdx (sd₂.castN h.n_eq.symm).pos j hj)
        rw [hh]
        congr 1
        · apply Fin.ext; exact hred_i_val
        · apply Fin.ext; exact hred_j_val
  · -- attach_eq
    intro i
    show unpeelAttach (sd₂.castN h.n_eq.symm) i
        = unpeelAttach sd₂ (Fin.cast hn_unp i)
    unfold unpeelAttach
    by_cases hi : i = (sd₂.castN h.n_eq.symm).pos
    · rw [dif_pos hi]
      have hi_cast : Fin.cast hn_unp i = sd₂.pos := by
        apply Fin.ext
        have : i.val = sd₂.pos.val := by
          have := congrArg Fin.val hi; simp [hposval] at this; exact this
        simp [Fin.cast, this]
      rw [dif_pos hi_cast]
      rfl
    · rw [dif_neg hi]
      have hi_cast_ne : Fin.cast hn_unp i ≠ sd₂.pos := by
        intro hcast; apply hi; apply Fin.ext
        have := congrArg Fin.val hcast
        simp [Fin.cast, hposval] at this ⊢; exact this
      rw [dif_neg hi_cast_ne]
      have hred_val :
          (Fin.cast h.n_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)).val
            = (reduceIdx sd₂.pos (Fin.cast hn_unp i) hi_cast_ne).val := by
        unfold reduceIdx
        by_cases hlt : i.val < ((sd₂.castN h.n_eq.symm).pos).val
        · have hlt' : (Fin.cast hn_unp i).val < sd₂.pos.val := by
            simp [Fin.cast]; rw [← hposval]; exact hlt
          rw [dif_pos hlt, dif_pos hlt']; rfl
        · have hlt' : ¬ ((Fin.cast hn_unp i).val < sd₂.pos.val) := by
            intro hh; apply hlt
            simp [Fin.cast] at hh; rw [hposval]; exact hh
          rw [dif_neg hlt, dif_neg hlt']; rfl
      have hh := h.attach_eq (reduceIdx (sd₂.castN h.n_eq.symm).pos i hi)
      rw [hh]
      congr 1
      apply Fin.ext; exact hred_val

/-! ### Terminal-to-root replay interpreter -/

namespace PeelChain

/-- **Σ-bundled structural recursion** producing both the replay
result and a proof that its packet count equals `R.n`. The size
witness is needed so the cons step can transport `sinkData R s`
along the IH's size equality. -/
def replayAux : ∀ {R : CompletedReconstructionRecord setup}, PeelChain R →
    { r : CompletedReconstructionRecord setup // r.n = R.n }
  | R, .nil _ _ => ⟨R, rfl⟩
  | R, .cons _ s _ tail =>
    match replayAux tail with
    | ⟨r', hr'⟩ =>
      ⟨unpeelSink r' ((sinkData R s).castN hr'.symm), by
        show r'.n + 1 = R.n
        have hp : (peelSink R s).n = R.n - 1 := rfl
        have hpos : 0 < R.n := by have := s.isLt; omega
        rw [hr', hp]; omega⟩

/-- **The genuine terminal-to-root replay interpreter.** Unlike
`reconstruct` (`UnpeelChain.lean`), `replay`'s cons case **consumes**
`replay tail` and unpeels the transported `sinkData R s` over it. -/
def replay {R : CompletedReconstructionRecord setup} (c : PeelChain R) :
    CompletedReconstructionRecord setup :=
  (replayAux c).1

/-- The replay result has the same packet count as the original record. -/
theorem replay_n {R : CompletedReconstructionRecord setup} (c : PeelChain R) :
    (replay c).n = R.n :=
  (replayAux c).2

/-- Computational reduction for `replay` on the `nil` constructor. -/
@[simp] theorem replay_nil
    (R : CompletedReconstructionRecord setup) (h : R.n = 0) :
    replay (.nil R h) = R := rfl

/-- Computational reduction for `replay` on the `cons` constructor. -/
theorem replay_cons
    (R : CompletedReconstructionRecord setup) (s : Fin R.n)
    (hSink : R.IsSink s) (tail : PeelChain (peelSink R s)) :
    replay (.cons R s hSink tail)
      = unpeelSink (replay tail)
          ((sinkData R s).castN (replay_n tail).symm) := rfl

/-- **Headline: terminal-to-root replay interpreter is correct.**

Walking the chain bottom-up, applying `unpeelSink` at each `cons`
step against the previously-computed tail replay (with `sinkData`
transported through the chain's accumulated size equality), produces
a record `RecordEquiv` to the original `R`.

**Proof structure** (per `INV PeelChain-Replay`):

* **Base** (`nil`): `replay (nil R _) = R`, closed by `RecordEquiv.refl`.
* **Step** (`cons R s hSink tail`):
  1. IH on `tail` gives `RecordEquiv (replay tail) (peelSink R s)`.
  2. `unpeelSink_castN_recordEquiv` with that IH and `sinkData R s`
     yields `RecordEquiv (unpeelSink (replay tail) (sd_transported))
     (unpeelSink (peelSink R s) (sinkData R s))`.
  3. The right-hand side is `RecordEquiv` to `R` by `unpeelSink_peelSink R s hSink`.
  4. Compose by `RecordEquiv.trans`.

Per the `INV PeelChain-Replay` invariant: this is genuine terminal-residue
replay, not the prefix-local form of `reconstruct_recordEquiv`. -/
theorem replay_recordEquiv :
    ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
      RecordEquiv (replay c) R
  | R, .nil _ _ => RecordEquiv.refl R
  | R, .cons _ s hSink tail => by
    have ih : RecordEquiv (replay tail) (peelSink R s) := replay_recordEquiv tail
    have step1 :
        RecordEquiv
          (unpeelSink (replay tail) ((sinkData R s).castN ih.n_eq.symm))
          (unpeelSink (peelSink R s) (sinkData R s)) :=
      unpeelSink_castN_recordEquiv ih (sinkData R s)
    have step2 :
        RecordEquiv (unpeelSink (peelSink R s) (sinkData R s)) R :=
      unpeelSink_peelSink R s hSink
    -- The replay-cons reduction uses `(replay_n tail).symm` whereas step1
    -- uses `ih.n_eq.symm`; both are propositional equalities of the same
    -- two Nat values, so they agree by Lean 4's propositional proof
    -- irrelevance and the goal closes by `rfl` after the rewrite.
    have hsd_eq :
        (sinkData R s).castN (replay_n tail).symm
          = (sinkData R s).castN ih.n_eq.symm := rfl
    show RecordEquiv
        (unpeelSink (replay tail) ((sinkData R s).castN (replay_n tail).symm))
        R
    rw [hsd_eq]
    exact RecordEquiv.trans step1 step2

/-! ### Stability under equivalent peel chains (Phase 3B item 5c) -/

/-- **Replay stability under chain choice.** Any two peel chains on the
same record `R` replay to records that are `RecordEquiv`.

This is the first rung of canonical/uniqueness for completed
reconstruction: although different sink-orderings produce different
intermediate `peelSink`s and different chain shapes, the **terminal
result** of replay is invariant up to `RecordEquiv`. The proof is
immediate by transitivity of `RecordEquiv`:

```
replay c  ≃  R  ≃  replay c'
```

Per the new `INV Replay-Transport` invariant: this stability follows
purely from `RecordEquiv` + transport, never from definitional equality
of the chain shapes. It is the manuscript-level seed for moving from
"completed reconstruction exists" toward "completed reconstruction is
canonical/unique up to administrative equivalence" (the future
`canonicalWord_replays` direction).

Manuscript anchor: `our_paper_draft.tex` L1180
(`thm:canonical-reconstruction-algorithm`) — the canonicality clause
that any two valid recursive descents arrive at the same completed
reconstruction up to record equivalence. -/
theorem replay_stable
    {R : CompletedReconstructionRecord setup} (c c' : PeelChain R) :
    RecordEquiv (replay c) (replay c') :=
  RecordEquiv.trans (replay_recordEquiv c) (RecordEquiv.symm (replay_recordEquiv c'))

/-
TEX ref: our_paper_draft.tex, label prop:reconstruction-uniqueness (L1178+)
Paper role: the canonical reconstruction is unique up to record equivalence;
  any two canonical chains over the same record produce record-equivalent replays
Lean status: MISSING → stub added (M2); proof follows from replay_stable
-/
/-- **`prop:reconstruction-uniqueness`**: canonical reconstruction is unique
up to record equivalence.

Any two peel chains over the same completed record produce replay results
that are record-equivalent. This is the paper's uniqueness clause: the
completed reconstruction of a record is canonical up to the administrative
equivalence encoded by `RecordEquiv`. -/
theorem reconstruction_uniqueness
    {setup : RewriteCalculusSetup.{u}}
    {R : CompletedReconstructionRecord setup}
    (c c' : PeelChain R) :
    RecordEquiv (replay c) (replay c') :=
  replay_stable c c'

/-
TEX ref: our_paper_draft.tex, label cor:reconstruction-retraction (L1182+)
Paper role: the canonical peel-chain replay is a retraction of the
  completed record, i.e., replay returns something record-equivalent to R
Lean status: MISSING → stub added (M2); proof is replay_recordEquiv
-/
/-- **`cor:reconstruction-retraction`**: the replay of any peel chain over `R`
is record-equivalent to `R` itself (replay is a retraction).

This is an immediate corollary of `replay_recordEquiv`: any peel chain
faithfully reconstructs the record up to `RecordEquiv`. -/
theorem reconstruction_retraction
    {setup : RewriteCalculusSetup.{u}}
    {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) :
    RecordEquiv (replay c) R :=
  replay_recordEquiv c

end PeelChain

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
