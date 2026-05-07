import TraceCalc.LayerB.RealObjects.Frontier

/-!
# Real-objects formalization: contextual/deep adjacent admin swaps (item 5h)

**Phase 3B item 5h (2026-04-24).** Per user's verbatim 5h directive:
lift the `k = 2` frontier theorem (item 5g) to **adjacent swaps
occurring after an arbitrary common prefix**. The truncated frontier
canonicality content of `thm:canonical-reconstruction-algorithm`
(L1180) is not just "the first two peel choices commute" but "any
local independent adjacent swap *anywhere* in the peel history
preserves the truncated frontier modulo boundary administration."

## Architecture

* `PeelChain.ContextualAdminMove d c₁ c₂` — depth-indexed admin
  relation: `c₁` and `c₂` differ by an adjacent swap occurring after
  a common cons-prefix of length `d`.
  - `here`: depth-0, reuse the existing `AdminMove c₁ c₂`.
  - `under_cons`: push the move under one more layer of common cons.
* `ContextualAdminMove.residueAt_structEquiv_admin` — the contextual
  residue theorem: at depth `d`, the residues at `d + 2` are
  `RecordStructEquiv BoundaryAdminEquiv`.
  - depth-0 case directly consumes
    `AdminMove.residueAt_2_structEquiv_admin` (item 5g);
  - inductive step is pure rfl-reduction via `residueAt_cons_succ`
    (`residueAt (cons _) (k+1) = residueAt tail k`).

## Why this is the next canonicality layer

The depth-`d` truncated residue exposes the genuine intermediate
record after `d + 2` peel steps; under a contextual swap at depth
`d`, the first `d` steps are literally shared and the next two
steps diverge in the local-swap manner already proved at
`peelSink_swap_structEquiv_admin`. The proof therefore reduces to
the depth-0 frontier theorem after a simple rfl-unfolding of
`residueAt` through the common cons-prefix — **without** routing
through `replay_stable`.

Per `INV AdminMove-Nonvacuity`: this layer continues to consume the
local two-step swap content non-vacuously. Replay-level reasoning is
explicitly avoided.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **contextual swap content** this layer provides.
* L1186–L1192 — the per-step descent whose adjacent independent-sink
  swaps may occur at *any* depth in the chain, not just at the head.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

namespace PeelChain

/-! ### Depth-indexed contextual admin move -/

/-- **Contextual admin move at depth `d`.**

`ContextualAdminMove d c₁ c₂` says: chains `c₁` and `c₂` differ by
a single adjacent independent-sink swap **occurring after a common
cons-prefix of length `d`**.

* `here h`: depth-0 contextual move — `c₁` and `c₂` are already in
  the head-prefix swap shape of `AdminMove`.
* `under_cons s hSink m`: push the move under one more cons,
  incrementing the depth by `1`. Both chains start with the **same**
  `cons R s hSink _`; the move occurs in their shared tail
  continuation.

This is precisely the manuscript's "adjacent swap at any depth in
the peel history" relation, presented inductively so the depth is a
syntactically tracked index. -/
inductive ContextualAdminMove :
    ∀ {R : CompletedReconstructionRecord setup},
      Nat → PeelChain R → PeelChain R → Prop
  | here
      {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
      (h : AdminMove c₁ c₂) :
      ContextualAdminMove 0 c₁ c₂
  | under_cons
      {R : CompletedReconstructionRecord setup} (s : Fin R.n)
      (hSink : R.IsSink s)
      {tail₁ tail₂ : PeelChain (peelSink R s)} {d : Nat}
      (m : ContextualAdminMove d tail₁ tail₂) :
      ContextualAdminMove (d + 1)
        (.cons R s hSink tail₁) (.cons R s hSink tail₂)

namespace ContextualAdminMove

/-- **Smart constructor at depth `0`.** Lift any head-prefix
`AdminMove` to a contextual move. -/
theorem ofAdminMove
    {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
    (h : AdminMove c₁ c₂) : ContextualAdminMove 0 c₁ c₂ :=
  .here h

/-! ### The contextual residue theorem -/

/-- **The contextual truncated-frontier canonicality theorem
(Phase 3B item 5h).**

For any `ContextualAdminMove d c₁ c₂`, the **truncated residues at
depth `d + 2`** are `RecordStructEquiv BoundaryAdminEquiv`.

**Proof structure**: induct on the contextual move.

* `here h`: the goal is the head-prefix theorem at `d = 0`, i.e.
  residues at `0 + 2 = 2` for an `AdminMove c₁ c₂`. Direct
  consumption of `AdminMove.residueAt_2_structEquiv_admin` (item 5g).
* `under_cons s hSink m ih`: the goal is at index `(d + 1) + 2`. By
  `residueAt_cons_succ` (rfl), each residue
  `residueAt (.cons R s hSink tailᵢ) ((d + 1) + 2)` reduces to
  `residueAt tailᵢ (d + 2)`, which is exactly the IH.

**Per `INV AdminMove-Nonvacuity`**: at the `here` constructor the
proof routes through item 5g's `residueAt_2_structEquiv_admin`
(which itself routes through `frontier_structEquiv_admin` =
`peelSink_swap_structEquiv_admin`), so the local two-step swap
content is consumed non-vacuously at every depth. The inductive
step is a pure structural rfl-reduction — it adds no replay-level
content. -/
theorem residueAt_structEquiv_admin
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (PeelChain.residueAt c₁ (d + 2))
      (PeelChain.residueAt c₂ (d + 2)) := by
  induction m with
  | here h =>
    -- Goal: RecordStructEquiv … (residueAt c₁ 2) (residueAt c₂ 2)
    -- Direct consumption of item 5g, which itself consumes
    -- frontier_structEquiv_admin = peelSink_swap_structEquiv_admin.
    exact AdminMove.residueAt_2_structEquiv_admin h
  | @under_cons R s hSink tail₁ tail₂ d _ ih =>
    -- Goal: RecordStructEquiv …
    --   (residueAt (.cons R s hSink tail₁) ((d + 1) + 2))
    --   (residueAt (.cons R s hSink tail₂) ((d + 1) + 2))
    -- Both sides rfl-reduce via residueAt_cons_succ to
    --   residueAt tailᵢ (d + 2)
    -- which is exactly the inductive hypothesis.
    exact ih

end ContextualAdminMove

end PeelChain

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
