import TraceCalc.LayerB.RealObjects.AdminMove

/-!
# Real-objects formalization: truncated frontier replay (item 5g)

**Phase 3B item 5g (2026-04-24).** Per user's verbatim 5g directive +
`INV AdminMove-Nonvacuity`: introduce the **truncated/frontier
residue** of a `PeelChain` after the first `k` peeling steps, then
prove the adjacent-swap admin theorem at depth `k = 2` by **directly
consuming `AdminMove.frontier_structEquiv_admin`**, never routing
through full replay back to `R`.

Per the user's 5f → 5g analysis, full replay proves only **inverse
correctness** (`replay c ≃ R`); the substantive **canonicality**
content of `thm:canonical-reconstruction-algorithm` lives at the
*frontier* — the truncated residue at intermediate depth `k`.

## Architecture

* `PeelChain.residueAt c k` — the residue record after the first `k`
  peeling steps (lives in the inductive's home namespace
  `RewriteCalculusSetup.CompletedReconstructionRecord.PeelChain`).
* `residueAt_one_cons`, `residueAt_two_cons_cons` — explicit `rfl`
  characterizations of the truncated residue at `k = 1` and `k = 2`.
* `AdminMove.residueAt_2_structEquiv_admin` — **THE NONVACUITY GATE**
  (lives at `RewriteCalculusSetup.PeelChain.AdminMove`, the parallel
  namespace where `AdminMove.lean` declares `AdminMove`/`AdminEquiv`).
  Proof: `cases h; exact frontier_structEquiv_admin h`.
* `AdminEquiv.residueAt_2_structEquiv_admin` — closure-lifted form.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **truncated frontier** content this theorem realizes.
* L1186–L1192 — the per-step descent run to fixed truncation depth.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### Truncated frontier residue

Defined in the inductive's home namespace
`CompletedReconstructionRecord.PeelChain` so that `c.residueAt k`
dot-notation resolves correctly. -/

namespace CompletedReconstructionRecord
namespace PeelChain

/-- **Auxiliary**: `residueAtAux k c` recurses primarily on `k`,
giving clean rfl-equations for all three pattern clauses
(`k = 0`, `k+1` on `.nil`, `k+1` on `.cons`). -/
def residueAtAux : ∀ (_ : Nat) {R : CompletedReconstructionRecord setup},
    PeelChain R → CompletedReconstructionRecord setup
  | 0, R, _ => R
  | _ + 1, _, .nil R _ => R
  | n + 1, _, .cons _ _ _ tail => residueAtAux n tail

/-- **The residue record after the first `k` peeling steps of `c`.**

User-facing wrapper around `residueAtAux` with the natural argument
order `c k`. Equation rules (all by `rfl`):
* `residueAt c 0 = R`;
* `residueAt (.nil R _) (k + 1) = R`;
* `residueAt (.cons _ _ _ tail) (k + 1) = residueAt tail k`.

This is the **truncated** counterpart to `replay`. -/
def residueAt {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (k : Nat) : CompletedReconstructionRecord setup :=
  residueAtAux k c

/-- **Equation lemma at `k = 0`.** -/
@[simp] theorem residueAt_zero
    {R : CompletedReconstructionRecord setup} (c : PeelChain R) :
    residueAt c 0 = R := rfl

/-- **Equation lemma at the empty chain, `k > 0`.** -/
@[simp] theorem residueAt_nil_succ
    (R : CompletedReconstructionRecord setup) (h : R.n = 0) (k : Nat) :
    residueAt (.nil R h) (k + 1) = R := rfl

/-- **Equation lemma at the cons constructor, `k > 0`.** -/
@[simp] theorem residueAt_cons_succ
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (tail : PeelChain (peelSink R s)) (k : Nat) :
    residueAt (.cons R s hSink tail) (k + 1) = residueAt tail k := rfl

/-- **Specialization at `k = 1`.** -/
theorem residueAt_one_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (tail : PeelChain (peelSink R s)) :
    residueAt (.cons R s hSink tail) 1 = peelSink R s := rfl

/-- **Specialization at `k = 2`** — the depth at which the adjacent-swap
admin theorem lives. -/
theorem residueAt_two_cons_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (s' : Fin (peelSink R s).n)
    (hSink' : (peelSink R s).IsSink s')
    (tail' : PeelChain (peelSink (peelSink R s) s')) :
    residueAt
        (.cons R s hSink (.cons (peelSink R s) s' hSink' tail')) 2
      = peelSink (peelSink R s) s' := rfl

end PeelChain
end CompletedReconstructionRecord

/-! ### Truncated frontier admin theorems

The `AdminMove`/`AdminEquiv` types from `AdminMove.lean` live at
`RewriteCalculusSetup.PeelChain.AdminMove` (a parallel `PeelChain`
sub-namespace). We open the inductive's home namespace so the
unqualified `residueAt` resolves to the just-defined function. -/

open CompletedReconstructionRecord.PeelChain

namespace PeelChain
namespace AdminMove

/-- **The truncated frontier nonvacuity gate (Phase 3B item 5g).**

For any `AdminMove.adjacent_swap` between `c₁ : PeelChain R` and
`c₂ : PeelChain R`, the **truncated residues at depth `k = 2`** are
`RecordStructEquiv BoundaryAdminEquiv`.

**Per `INV AdminMove-Nonvacuity`**: this proof **directly consumes
the local two-step swap content** via `frontier_structEquiv_admin`
(equivalently, `peelSink_swap_structEquiv_admin`). It does **not**
route through `PeelChain.replay`/`replay_recordEquiv`/`replay_stable`. -/
theorem residueAt_2_structEquiv_admin
    {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
    (h : AdminMove c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (residueAt c₁ 2) (residueAt c₂ 2) := by
  cases h with
  | adjacent_swap h _ _ _ _ =>
    -- LHS/RHS reduce by rfl (residueAt_two_cons_cons) to
    --   peelSink (peelSink R s) (peelSinkOtherIdx s t _)
    --   peelSink (peelSink R t) (peelSinkOtherIdx t s _)
    -- Direct frontier consumption — NOT routed through replay.
    exact frontier_structEquiv_admin h

end AdminMove

namespace AdminEquiv

/-- **Closure-lifted truncated frontier theorem** under the generated
chain equivalence `AdminEquiv`. -/
theorem residueAt_2_structEquiv_admin
    {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
    (h : AdminEquiv c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (residueAt c₁ 2) (residueAt c₂ 2) := by
  induction h with
  | refl c =>
    exact RecordStructEquiv.refl
      (fun Y => BoundaryAdminEquiv.refl Y) (residueAt c 2)
  | symm _ ih =>
    exact ih.symm (fun hY => hY.symm)
  | trans _ _ ih₁ ih₂ =>
    exact ih₁.trans (fun hY₁ hY₂ => hY₁.trans hY₂) ih₂
  | ofMove m =>
    exact AdminMove.residueAt_2_structEquiv_admin m

end AdminEquiv

end PeelChain

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc
