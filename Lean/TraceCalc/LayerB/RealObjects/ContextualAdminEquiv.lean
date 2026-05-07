import TraceCalc.LayerB.RealObjects.ContextualAdminMove

/-!
# Real-objects formalization: contextual admin equivalence closure (items 5i–5m)

**Phase 3B items 5i–5m (2026-04-24).** This file delivers the
**administrative confluence skeleton** at the contextual / depth-indexed
level: the equivalence closure of `ContextualAdminMove`, the residue
theorem for the closure, depth-polymorphic API, a depth-erased
`AnyContextual…` layer, the canonical frontier-observation packaging,
and manuscript-facing theorem aliases.

## Items in this file

* **5i** — `PeelChain.ContextualAdminEquiv d c₁ c₂` closure +
  `residueAt_structEquiv_admin` for the closure.
* **5j** — Smart constructors and prefix `rfl`/simp lemmas for
  `residueAt` under common cons-prefixes.
* **5k** — `PeelChain.AnyContextualAdminMove c₁ c₂` (depth-erased ∃)
  and `AnyContextualAdminEquiv c₁ c₂`. **Honest scope** (per stop
  condition): NO unified residue theorem on the depth-erased layer
  (the residue comparison happens at `d + 2`, so depth is semantic
  data and cannot be quietly forgotten); embedding theorems only.
* **5l** — `FrontierObservation` Σ-bundle + induced relation +
  `ContextualAdminMove`-to-equivalent-observations theorem.
* **5m** — Manuscript-facing theorem aliases.

## Global invariants honored

* `INV AdminMove-Nonvacuity`: every closure / residue theorem in this
  file ultimately routes through
  `AdminMove.frontier_structEquiv_admin = peelSink_swap_structEquiv_admin`
  via item 5g (`AdminMove.residueAt_2_structEquiv_admin`) and item 5h
  (`ContextualAdminMove.residueAt_structEquiv_admin`). NO route through
  `replay_recordEquiv` / `replay_stable`.
* `INV Frontier-Recursion`: applied in 5g's `residueAtAux` helper.
* `INV Build-Trust-Gate`: this batch was validated by full `lake build`
  (not grepped output) before status sync.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **administrative confluence** content this layer
  realizes: the equivalence closure of contextual independent-sink
  swaps preserves the truncated frontier modulo boundary admin.
* L1186–L1192 — the per-step descent.
* L1224 (`def:boundary-exposure`) — the per-step boundary exposure
  whose chain of administrative reorderings is exposed here.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects
namespace RewriteCalculusSetup

open CompletedReconstructionRecord
open CompletedReconstructionRecord.PeelChain

variable {setup : RewriteCalculusSetup.{u}}

namespace PeelChain

/-! ## Item 5i — Contextual admin equivalence closure -/

/-- **Equivalence closure of `ContextualAdminMove` at depth `d`.**

Two `PeelChain` instances over the same `R` are **contextually admin
equivalent at depth `d`** when they differ by a finite sequence of
`refl`/`symm`/`trans` steps over the depth-`d` contextual move
relation `ContextualAdminMove d`.

Per `INV AdminMove-Nonvacuity`: the only non-vacuous constructor is
`ofMove` — `refl`/`symm`/`trans` are pure equivalence-relation
algebra. Every consumer extracting structural canonicality content
must descend through `ofMove` to a real
`ContextualAdminMove d c₁ c₂` and ultimately to
`peelSink_swap_structEquiv_admin`. -/
inductive ContextualAdminEquiv :
    ∀ {R : CompletedReconstructionRecord setup},
      Nat → PeelChain R → PeelChain R → Prop
  | refl
      {R : CompletedReconstructionRecord setup} {d : Nat} (c : PeelChain R) :
      ContextualAdminEquiv d c c
  | symm
      {R : CompletedReconstructionRecord setup} {d : Nat}
      {c₁ c₂ : PeelChain R}
      (h : ContextualAdminEquiv d c₁ c₂) :
      ContextualAdminEquiv d c₂ c₁
  | trans
      {R : CompletedReconstructionRecord setup} {d : Nat}
      {c₁ c₂ c₃ : PeelChain R}
      (h₁ : ContextualAdminEquiv d c₁ c₂)
      (h₂ : ContextualAdminEquiv d c₂ c₃) :
      ContextualAdminEquiv d c₁ c₃
  | ofMove
      {R : CompletedReconstructionRecord setup} {d : Nat}
      {c₁ c₂ : PeelChain R}
      (m : ContextualAdminMove d c₁ c₂) :
      ContextualAdminEquiv d c₁ c₂

namespace ContextualAdminEquiv

/-! ### Equivalence-relation API aliases (5i.2) -/

/-- API alias for `ContextualAdminEquiv.refl`. -/
theorem refl' {R : CompletedReconstructionRecord setup}
    (d : Nat) (c : PeelChain R) : ContextualAdminEquiv d c c :=
  @ContextualAdminEquiv.refl _ _ d c

/-- API alias for `ContextualAdminEquiv.symm`. -/
theorem symm' {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    ContextualAdminEquiv d c₂ c₁ :=
  .symm h

/-- API alias for `ContextualAdminEquiv.trans`. -/
theorem trans' {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ c₃ : PeelChain R}
    (h₁ : ContextualAdminEquiv d c₁ c₂)
    (h₂ : ContextualAdminEquiv d c₂ c₃) :
    ContextualAdminEquiv d c₁ c₃ :=
  .trans h₁ h₂

/-- API alias for `ContextualAdminEquiv.ofMove`. -/
theorem ofMove' {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    ContextualAdminEquiv d c₁ c₂ :=
  .ofMove m

/-! ### Closure-lifted residue theorem (5i.3 + 5i.4 nonvacuity gate) -/

/-- **The closure-lifted contextual residue theorem.**

For any `ContextualAdminEquiv d c₁ c₂`, the truncated residues at
depth `d + 2` are `RecordStructEquiv BoundaryAdminEquiv`.

**Proof structure**: induct on the closure constructors.

* `refl _ c`: same chain, residues are literally equal — closed by
  `RecordStructEquiv.refl` against `BoundaryAdminEquiv.refl`.
* `symm h`: invoke `RecordStructEquiv.symm` against
  `BoundaryAdminEquiv.symm`.
* `trans h₁ h₂`: invoke `RecordStructEquiv.trans` against
  `BoundaryAdminEquiv.trans`.
* `ofMove m`: **the nonvacuity gate** — invoke
  `ContextualAdminMove.residueAt_structEquiv_admin m` (item 5h),
  which itself routes through `AdminMove.residueAt_2_structEquiv_admin`
  (item 5g) and `peelSink_swap_structEquiv_admin` (item 5e-ii).

**Per `INV AdminMove-Nonvacuity`**: the `ofMove` case carries the
genuine swap content; equivalence-relation cases are pure algebraic
closure. NO routing through `PeelChain.replay_stable`. -/
theorem residueAt_structEquiv_admin
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (residueAt c₁ (d + 2)) (residueAt c₂ (d + 2)) := by
  induction h with
  | refl c =>
    exact RecordStructEquiv.refl
      (fun Y => BoundaryAdminEquiv.refl Y) _
  | symm _ ih =>
    exact ih.symm (fun hY => hY.symm)
  | trans _ _ ih₁ ih₂ =>
    exact ih₁.trans (fun hY₁ hY₂ => hY₁.trans hY₂) ih₂
  | ofMove m =>
    exact ContextualAdminMove.residueAt_structEquiv_admin m

end ContextualAdminEquiv

/-! ## Item 5j — Smart constructors + prefix simp lemmas -/

namespace ContextualAdminMove

/-- **Smart constructor**: lift any head-prefix `AdminMove` to a
contextual move at depth `0`. Same as `ofAdminMove` defined in
`ContextualAdminMove.lean`; re-exported here for symmetry with the
`under_one_cons` / `under_two_cons` smart constructors below. -/
theorem of_admin_move
    {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
    (h : AdminMove c₁ c₂) : ContextualAdminMove 0 c₁ c₂ :=
  .here h

/-- **Smart constructor at depth `1`**: a contextual swap occurring
under a single common cons-prefix. -/
theorem under_one_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) {tail₁ tail₂ : PeelChain (peelSink R s)}
    (h : AdminMove tail₁ tail₂) :
    ContextualAdminMove 1
      (.cons R s hSink tail₁) (.cons R s hSink tail₂) :=
  .under_cons s hSink (.here h)

/-- **Smart constructor at depth `2`**: a contextual swap occurring
under a two-cons common prefix. -/
theorem under_two_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (s' : Fin (peelSink R s).n)
    (hSink' : (peelSink R s).IsSink s')
    {tail₁ tail₂ : PeelChain (peelSink (peelSink R s) s')}
    (h : AdminMove tail₁ tail₂) :
    ContextualAdminMove 2
      (.cons R s hSink (.cons (peelSink R s) s' hSink' tail₁))
      (.cons R s hSink (.cons (peelSink R s) s' hSink' tail₂)) :=
  .under_cons s hSink (.under_cons s' hSink' (.here h))

end ContextualAdminMove

/-! ### Prefix simp lemmas for `residueAt` (5j.6)

Three explicit specializations of `residueAt_cons_succ`. The general
`residueAt_cons_succ` already exists from item 5g; these are
named-pretty restatements at depth `1` and `2` for downstream
ergonomics. -/

/-- `residueAt` under one common cons strips the cons. -/
@[simp] theorem residueAt_under_one_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (tail : PeelChain (peelSink R s)) (k : Nat) :
    residueAt (.cons R s hSink tail) (k + 1) = residueAt tail k := rfl

/-- `residueAt` under two common cons strips both cons. -/
@[simp] theorem residueAt_under_two_cons
    {R : CompletedReconstructionRecord setup} (s : Fin R.n)
    (hSink : R.IsSink s) (s' : Fin (peelSink R s).n)
    (hSink' : (peelSink R s).IsSink s')
    (tail : PeelChain (peelSink (peelSink R s) s')) (k : Nat) :
    residueAt
        (.cons R s hSink (.cons (peelSink R s) s' hSink' tail)) (k + 2)
      = residueAt tail k := rfl

/-! ## Item 5k — Depth-erased `AnyContextual…` layer

**Honest scope (per user's stop condition)**: depth is semantic data
for the residue comparison (residues at `d + 2` between two chains);
the depth-erased layer therefore exposes **only the existence of some
depth at which the chains differ by a single contextual move**, and
the equivalence closure thereof. NO unified residue theorem is stated
at the depth-erased level — to obtain a residue comparison, the
consumer must `obtain ⟨d, m⟩ := h` and apply
`ContextualAdminMove.residueAt_structEquiv_admin` at depth `d`. -/

/-- **Depth-erased contextual move**: there exists some depth `d` at
which `c₁` and `c₂` differ by a single `ContextualAdminMove`. -/
def AnyContextualAdminMove
    {R : CompletedReconstructionRecord setup}
    (c₁ c₂ : PeelChain R) : Prop :=
  ∃ d, ContextualAdminMove d c₁ c₂

/-- **Equivalence closure of depth-erased contextual moves.** -/
inductive AnyContextualAdminEquiv :
    ∀ {R : CompletedReconstructionRecord setup}, PeelChain R → PeelChain R → Prop
  | refl
      {R : CompletedReconstructionRecord setup} (c : PeelChain R) :
      AnyContextualAdminEquiv c c
  | symm
      {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
      (h : AnyContextualAdminEquiv c₁ c₂) :
      AnyContextualAdminEquiv c₂ c₁
  | trans
      {R : CompletedReconstructionRecord setup} {c₁ c₂ c₃ : PeelChain R}
      (h₁ : AnyContextualAdminEquiv c₁ c₂)
      (h₂ : AnyContextualAdminEquiv c₂ c₃) :
      AnyContextualAdminEquiv c₁ c₃
  | ofMove
      {R : CompletedReconstructionRecord setup} {c₁ c₂ : PeelChain R}
      (m : AnyContextualAdminMove c₁ c₂) :
      AnyContextualAdminEquiv c₁ c₂

namespace AnyContextualAdminMove

/-- **Embedding**: every depth-`d` contextual move embeds into the
depth-erased layer. -/
theorem ofContextualAdminMove
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    AnyContextualAdminMove c₁ c₂ :=
  ⟨d, m⟩

end AnyContextualAdminMove

namespace AnyContextualAdminEquiv

/-- **Embedding**: every depth-`d` `ContextualAdminEquiv` embeds into
the depth-erased equivalence closure. By induction on the closure
constructors, mapping each constructor to its depth-erased counterpart;
the `ofMove` case routes through
`AnyContextualAdminMove.ofContextualAdminMove`. -/
theorem ofContextualAdminEquiv
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    AnyContextualAdminEquiv c₁ c₂ := by
  induction h with
  | refl _ => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | ofMove m => exact .ofMove (.ofContextualAdminMove m)

end AnyContextualAdminEquiv

/-! ## Item 5l — Frontier observations -/

/-- **A frontier observation of a chain `c`**: a witness packaging a
truncation depth and the residue at depth `depth + 2`.

This bundles the canonical-frontier observation point in a single
structure so downstream theorems (canonical-word descent) can quote
"the depth-`d` frontier of chain `c`" as a single object rather than
threading two arguments. -/
structure FrontierObservation
    {R : CompletedReconstructionRecord setup} (c : PeelChain R) where
  /-- Truncation depth (residue is taken at `depth + 2`). -/
  depth : Nat
  /-- The residue record at the chosen depth. -/
  residue : CompletedReconstructionRecord setup
  /-- Coherence: the residue is exactly `residueAt c (depth + 2)`. -/
  residue_eq : residue = residueAt c (depth + 2)

namespace FrontierObservation

/-- **Canonical observation at depth `d`**: bundle `residueAt c (d+2)`
into a `FrontierObservation`. -/
def ofChain {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (d : Nat) : FrontierObservation c where
  depth := d
  residue := residueAt c (d + 2)
  residue_eq := rfl

/-- **Equivalence of frontier observations** induced by
`RecordStructEquiv BoundaryAdminEquiv`. Two observations are
*frontier-equivalent at common depth* when they live at the same
`depth` and their residues are `RecordStructEquiv BoundaryAdminEquiv`. -/
structure Equiv {R : CompletedReconstructionRecord setup}
    {c₁ c₂ : PeelChain R}
    (o₁ : FrontierObservation c₁) (o₂ : FrontierObservation c₂) : Prop where
  /-- Observations at the same truncation depth. -/
  depth_eq : o₁.depth = o₂.depth
  /-- Residues are admin-structurally equivalent. -/
  residue_struct_equiv :
    RecordStructEquiv (@BoundaryAdminEquiv setup) o₁.residue o₂.residue

/-- **A `ContextualAdminMove` at depth `d` produces equivalent
canonical frontier observations at depth `d`.**

This is the manuscript-facing packaging of item 5h's residue theorem
in `FrontierObservation`-language. The proof is direct unfolding +
`ContextualAdminMove.residueAt_structEquiv_admin`. -/
theorem ofContextualAdminMove
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    Equiv (ofChain c₁ d) (ofChain c₂ d) where
  depth_eq := rfl
  residue_struct_equiv :=
    ContextualAdminMove.residueAt_structEquiv_admin m

/-- **Closure-lifted version**: a `ContextualAdminEquiv` at depth `d`
also produces equivalent canonical frontier observations at depth `d`.
Routes through item 5i. -/
theorem ofContextualAdminEquiv
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    Equiv (ofChain c₁ d) (ofChain c₂ d) where
  depth_eq := rfl
  residue_struct_equiv :=
    ContextualAdminEquiv.residueAt_structEquiv_admin h

end FrontierObservation

/-! ## Item 5m — Manuscript-facing theorem aliases

These re-export the Lean-native theorem names under labels that
mirror the manuscript's wording for `thm:canonical-reconstruction-algorithm`
(L1180). They carry no new content — pure pointers. -/

/-- **Manuscript-facing alias**: contextual admin moves preserve the
truncated frontier modulo boundary administration. Pointer to
[`ContextualAdminMove.residueAt_structEquiv_admin`](item 5h). -/
theorem theorem_contextual_admin_move_frontier_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (m : ContextualAdminMove d c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (residueAt c₁ (d + 2)) (residueAt c₂ (d + 2)) :=
  ContextualAdminMove.residueAt_structEquiv_admin m

/-- **Manuscript-facing alias**: the equivalence closure of contextual
admin moves preserves the truncated frontier. Pointer to
[`ContextualAdminEquiv.residueAt_structEquiv_admin`](item 5i). -/
theorem theorem_contextual_admin_equiv_frontier_stable
    {R : CompletedReconstructionRecord setup} {d : Nat}
    {c₁ c₂ : PeelChain R} (h : ContextualAdminEquiv d c₁ c₂) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (residueAt c₁ (d + 2)) (residueAt c₂ (d + 2)) :=
  ContextualAdminEquiv.residueAt_structEquiv_admin h

/-- **Manuscript-facing alias**: `BoundaryAdminEquiv` is the
equivalence closure of two-step independent-sink swap labels. Pointer
to [`peelSink_swap_structEquiv_admin`](item 5e-ii) — the genuine
swap-square content underlying every admin theorem in this layer. -/
theorem theorem_boundary_admin_generated_by_two_step_swaps
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
      (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t)) :=
  peelSink_swap_structEquiv_admin h

end PeelChain

end RewriteCalculusSetup
end RealObjects
end LayerB
end TraceCalc
