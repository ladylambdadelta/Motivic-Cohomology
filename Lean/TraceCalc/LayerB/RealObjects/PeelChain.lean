import TraceCalc.LayerB.RealObjects.CanonicalSink

/-!
# Real-objects formalization: iterated sink peeling (recursion theorem, weakest safe form)

**Real-objects path, Phase 3A item 3 — sub-item 1 (2026-04-23).**

This file proves the **local-to-iterated bridge** for sink peeling:

> *Iterated intrinsic peeling is well-defined and preserves
> completedness at every step.*

The mathematical shape, with `R₀ := R` and `R_{k+1} := peelSink R_k s_k`:

* `IsCompleted(R_k)` for every `k`,
* `|R_{k+1}| = |R_k| − 1` (strict packet decrease),
* `R_n = R_∅` (terminal residual has zero packets).

**Weakest-safe-form scope (per user instruction).** This file does
**not** yet claim uniqueness of the canonical reconstruction word.
The sink at each stage is selected via classical choice from
`DepGraph.sink_exists`; **the residual record at each step is
intrinsic relative to the selected sink, but the chain as a whole is
choice-dependent** until the canonical sink selection is threaded
through. The chain produced by `fromCompleted` is therefore an
*admissible* peel chain, not yet the *canonical* one. The
strengthening to `s_k = canonicalSink R_k _` is provided in this
same file as `canonicalPeelChain` (Phase 3A item 3 sub-item 2),
which is genuinely intrinsic in the chain as a whole. Uniqueness of
the resulting reconstruction word is deferred to a subsequent
sub-item, after the canonical-order-extraction infrastructure is in
place.

**Manuscript reference.** This is the inductive substrate of the
recursion in `our_paper_draft.tex` `thm:canonical-reconstruction-algorithm`
(L1180), specifically the recursive descent of L1186–L1192 which the
manuscript performs by induction on the packet count and which uses
`lem:sink-peel-preserves-completedness` (L1191) at every step. Here
we expose the descent as a real first-class data structure
(`PeelChain`) plus three theorems making the manuscript's three
invariants formal.

## Contents

1. `PeelChain R` — inductive data: a finite chain of sink choices
   that exhausts all packets of `R`, ending at a residual record with
   `n = 0`.
2. `PeelChain.length` and `PeelChain.length_eq` — the chain length
   equals `R.n` (manuscript invariant: strict packet decrease).
3. `PeelChain.terminal` and `PeelChain.terminal_n_zero` — the terminal
   residual is the empty record (manuscript invariant: termination by
   `n`).
4. `PeelChain.fromCompleted` — given `R.IsCompleted`, classical choice
   produces a `PeelChain R`. **Existence and well-foundedness** of
   iterated intrinsic peeling.
5. `PeelChain.fromCompleted_isCompleted_step` — every step of the
   chain produced by `fromCompleted` carries an `IsCompleted` witness;
   completedness is preserved at every depth (manuscript invariant:
   completedness propagates through the descent).

The construction is at the level of *some* intrinsic sink choice; the
canonical choice and the resulting unique word will be threaded
through in a follow-up sub-item once the canonical sink selection is
strengthened to apply at every residual stage uniformly.
-/

namespace TraceCalc
namespace LayerB
namespace RealObjects

open RewriteCalculusSetup
open RewriteCalculusSetup.CompletedReconstructionRecord

universe u

namespace RewriteCalculusSetup
namespace CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### The peel chain as an inductive data structure -/

/-- **`PeelChain R`** — a finite chain of intrinsic sink choices that
exhausts the packets of `R`. The chain is *data*, not a proof; the
sink-witness `hSink` at each step ensures the next residual is built
by `peelSink R s` for an actual sink `s`, so the next residual is
again a `CompletedReconstructionRecord`.

This is the substrate of the recursion in
`thm:canonical-reconstruction-algorithm` (`our_paper_draft.tex`
L1180): it makes the manuscript's "by induction on the number of
packets" descent into a real inductive data type whose recursor is
the manuscript's recursion. -/
inductive PeelChain : CompletedReconstructionRecord setup → Type u where
  /-- Base case: the empty record (no packets left to peel). -/
  | nil (R : CompletedReconstructionRecord setup) (h : R.n = 0) :
      PeelChain R
  /-- Recursive case: a sink choice + a chain on the residual. -/
  | cons (R : CompletedReconstructionRecord setup) (s : Fin R.n)
      (hSink : R.IsSink s) (tail : PeelChain (peelSink R s)) :
      PeelChain R

namespace PeelChain

/-! ### Invariant 1: chain length equals `R.n` -/

/-- The length of a peel chain. -/
def length : ∀ {R : CompletedReconstructionRecord setup}, PeelChain R → Nat
  | _, .nil _ _ => 0
  | _, .cons _ _ _ tail => length tail + 1

/-- **Manuscript invariant: strict packet decrease.** The chain
length equals the packet count of the starting record. Each `cons`
step contributes `+1` to the length and `−1` to the residual's packet
count (per `peelSink`'s `n := R.n - 1`), so the chain *exactly*
exhausts the packets. -/
theorem length_eq :
    ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
      c.length = R.n
  | _, .nil _ h => by simp [length, h]
  | R, .cons _ s _ tail => by
      have ih : tail.length = (peelSink R s).n := length_eq tail
      have hpos : 0 < R.n :=
        Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
      show tail.length + 1 = R.n
      have hRn : (peelSink R s).n = R.n - 1 := rfl
      rw [ih, hRn]; omega

/-! ### Invariant 2: chain terminates at the empty record -/

/-- The terminal residual record reached by a peel chain. -/
def terminal : ∀ {R : CompletedReconstructionRecord setup},
    PeelChain R → CompletedReconstructionRecord setup
  | R, .nil _ _ => R
  | _, .cons _ _ _ tail => terminal tail

/-- **Manuscript invariant: termination by `n`.** The terminal
residual has zero packets — it is the manuscript's `R_∅`. -/
theorem terminal_n_zero :
    ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
      c.terminal.n = 0
  | _, .nil _ h => h
  | _, .cons _ _ _ tail => terminal_n_zero tail

/-! ### Invariant 3: completedness propagates along the chain

Every residual visited by the chain is a `CompletedReconstructionRecord`
**by construction** (the inductive datatype indexes its argument), but
to claim that each residual *is completed* (i.e., satisfies
`IsCompleted`) requires `sink_peel_preserves_completedness` at every
step. We track this via a chain-level predicate `Completes` and prove
it propagates. -/

/-- A peel chain *completes* `R` if every residual it visits is
`IsCompleted`. -/
def Completes :
    ∀ {R : CompletedReconstructionRecord setup}, PeelChain R → Prop
  | R, .nil _ _ => R.IsCompleted
  | R, .cons _ _ _ tail => R.IsCompleted ∧ Completes tail

/-- The terminal residual of a completing chain is itself completed. -/
theorem terminal_isCompleted {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) : Completes c → c.terminal.IsCompleted := by
  induction c with
  | nil R h => intro hC; exact hC
  | cons R s hSink tail ih =>
    intro hC
    have ⟨_, htail⟩ : R.IsCompleted ∧ Completes tail := hC
    exact ih htail

/-! ### Existence: classical recursive construction

We construct the chain together with its `Completes` witness in a
single recursion, using a `Σ`-type return value. This avoids a
separate strong-induction proof of completedness propagation. -/

/-- **Existence and well-foundedness of iterated intrinsic peeling.**

Given a completed reconstruction record `R` together with an
`IsCompleted` witness, classical choice (used only to select *some*
sink at each residual stage; the residual *records* themselves are
computed, not chosen) produces a `PeelChain R` *paired with* a proof
that the chain completes `R`. The recursion terminates because each
step strictly decreases `R.n` (per `peelSink`'s definition
`n := R.n - 1`).

**This is the weakest safe form of the sink-peel recursion theorem.**
It does *not* claim canonicality of the chain; only that *some*
intrinsic descent exists, is well-founded, and propagates
completedness at every step via `sink_peel_preserves_completedness`.
The canonical strengthening (selecting `canonicalSink R` at each
stage) is the next sub-item. -/
noncomputable def fromCompletedAux
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    {c : PeelChain R // Completes c} :=
  if hzero : R.n = 0 then
    ⟨PeelChain.nil R hzero, hC⟩
  else
    let hpos : 0 < R.n := Nat.pos_of_ne_zero hzero
    let hex := R.dep.sink_exists hpos
    let s : Fin R.n := hex.choose
    let hSink : R.IsSink s := hex.choose_spec
    let hC' : (peelSink R s).IsCompleted :=
      sink_peel_preserves_completedness hSink hC
    let rest := fromCompletedAux (peelSink R s) hC'
    ⟨PeelChain.cons R s hSink rest.1, ⟨hC, rest.2⟩⟩
termination_by R.n
decreasing_by
  show (peelSink R s).n < R.n
  show R.n - 1 < R.n
  omega

/-- The chain extracted from `fromCompletedAux`. -/
noncomputable def fromCompleted
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    PeelChain R :=
  (fromCompletedAux R hC).1

/-- **Completeness propagation.** The chain produced by
`fromCompleted` satisfies `Completes`. -/
theorem fromCompleted_completes
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    Completes (fromCompleted R hC) :=
  (fromCompletedAux R hC).2

/-! ### Headline corollary -/

/-- **Headline: the local-to-iterated bridge.** Given a completed
reconstruction record `R`, there exists a peel chain that completes
`R` and ends at a residual with zero packets.

This is the precise theorem the user requested as the weakest safe
form of the sink-peel recursion theorem; it bundles invariants 1–3
above and is the substrate downstream consumers (canonical word
extraction, then full `thm:canonical-reconstruction-algorithm`) will
build on. -/
theorem iterated_peel_descent
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    ∃ c : PeelChain R, Completes c ∧ c.length = R.n ∧ c.terminal.n = 0 :=
  ⟨fromCompleted R hC,
    fromCompleted_completes R hC,
    length_eq _,
    terminal_n_zero _⟩

/-! ### Canonical peel chain (Phase 3A item 3 sub-item 2)

Replace the classical-choice sink selection of `fromCompleted` with
`canonicalSink R hpos` (the `Key`-greatest sink, from
[Lean/TraceCalc/LayerB/RealObjects/CanonicalSink.lean](CanonicalSink.lean)).
Each step is justified by `canonicalSink_isSink`. The residual is
still computed by `peelSink`, completedness propagation still uses
`sink_peel_preserves_completedness`, and termination is still by
strictly decreasing `R.n`. The result `canonicalPeelChain R hC` is a
chain whose sink at every depth is intrinsically determined by the
current residual — the **chain as a whole is canonical**, no longer
choice-dependent (modulo the noncomputable `Classical.choice` inside
the `Finset.max'`-based `canonicalSink`, which is deterministic).

This sub-item does **not** yet extract the canonical reconstruction
*order* (a function `Fin R.n → Fin R.n` recording the sink chosen at
each depth, lifted back into the original `R`'s frame via iterated
`embedSkip`); that requires an iterated-embedSkip lift and is a
separate sub-item. -/

/-- A peel chain is *canonical* if at every `cons` step the chosen
sink is the canonical sink of the current residual. -/
def IsCanonical :
    ∀ {R : CompletedReconstructionRecord setup}, PeelChain R → Prop
  | _, .nil _ _ => True
  | R, .cons _ s _ tail =>
      (∃ hpos : 0 < R.n, s = canonicalSink R hpos) ∧ IsCanonical tail

/-- Bundled canonical-chain construction: returns the chain together
with `Completes` and `IsCanonical` witnesses in one recursion. -/
noncomputable def canonicalPeelChainAux
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    {c : PeelChain R // Completes c ∧ IsCanonical c} :=
  if hzero : R.n = 0 then
    ⟨PeelChain.nil R hzero, hC, ⟨⟩⟩
  else
    let hpos : 0 < R.n := Nat.pos_of_ne_zero hzero
    let s : Fin R.n := canonicalSink R hpos
    let hSink : R.IsSink s := canonicalSink_isSink R hpos
    let hC' : (peelSink R s).IsCompleted :=
      sink_peel_preserves_completedness hSink hC
    let rest := canonicalPeelChainAux (peelSink R s) hC'
    ⟨PeelChain.cons R s hSink rest.1,
      ⟨hC, rest.2.1⟩,
      ⟨⟨hpos, rfl⟩, rest.2.2⟩⟩
termination_by R.n
decreasing_by
  show (peelSink R s).n < R.n
  show R.n - 1 < R.n
  omega

/-- **The canonical peel chain.** At every depth, the sink chosen is
`canonicalSink` of the current residual. The chain as a whole is
intrinsic to `R` (no classical choice over multiple admissible
sinks). -/
noncomputable def canonicalPeelChain
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    PeelChain R :=
  (canonicalPeelChainAux R hC).1

/-- **Completedness propagation along the canonical chain.** -/
theorem canonicalPeelChain_completes
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    Completes (canonicalPeelChain R hC) :=
  (canonicalPeelChainAux R hC).2.1

/-- **Required invariant 1**: every step of the canonical chain
selects `canonicalSink` of the current residual. -/
theorem canonicalPeelChain_isCanonical
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    IsCanonical (canonicalPeelChain R hC) :=
  (canonicalPeelChainAux R hC).2.2

/-- **Headline (canonical version): every completed reconstruction
record admits a canonical finite well-founded peel descent.**

For any completed `R`, the `canonicalPeelChain R hC` is a peel chain
of length exactly `R.n`, ending at the empty residual, with
completedness preserved at every step, and at every step the sink is
the `Key`-greatest sink of the current residual. -/
theorem canonical_iterated_peel_descent
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    Completes (canonicalPeelChain R hC) ∧
      IsCanonical (canonicalPeelChain R hC) ∧
      (canonicalPeelChain R hC).length = R.n ∧
      (canonicalPeelChain R hC).terminal.n = 0 :=
  ⟨canonicalPeelChain_completes R hC,
    canonicalPeelChain_isCanonical R hC,
    length_eq _,
    terminal_n_zero _⟩

/-! ### Canonical reconstruction order (Phase 3A item 3 sub-item 3)

The canonical peel chain selects, at each depth `k`, a sink
`s_k : Fin R_k.n` of the *current residual* `R_k`. To recover an
order on the **original** `R`'s packets, we must lift each `s_k`
back through the cascade

  `Fin R_k.n  ─embedSkip s_{k-1}→  Fin R_{k-1}.n  ─embedSkip s_{k-2}→  …  →  Fin R.n`.

`PeelChain.toOrder` performs this lift structurally on the chain:
the head is `s` (already in `Fin R.n`), and the tail's order, which
lives in `Fin (peelSink R s).n = Fin (R.n - 1)`, is mapped through
`embedSkip s` to land in `Fin R.n`.

**Scope of this sub-item (per user)**: we extract a canonical
**order** of original-frame packet indices — a `List (Fin R.n)` of
length exactly `R.n` with no duplicates — together with a
characterization that the head equals the canonical sink of `R`.
We do **not** yet construct a canonical reconstruction *word*
(which requires plugging the per-stage canonical primitive certified
declarations into the order via the manuscript's replay), nor any
uniqueness theorem. Those are subsequent sub-items. -/

/-- The list of original-frame packet indices visited by a peel
chain, in descent order. Each tail-frame index is lifted back
through `embedSkip s` of the corresponding `cons` step. -/
def toOrder : ∀ {R : CompletedReconstructionRecord setup},
    PeelChain R → List (Fin R.n)
  | _, .nil _ _ => []
  | _, .cons _ s _ tail => s :: tail.toOrder.map (embedSkip s)

/-- The canonical descent order has length `R.n`. -/
theorem toOrder_length :
    ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
      c.toOrder.length = R.n
  | _, .nil _ h => by simp [toOrder, h]
  | R, .cons _ s _ tail => by
    have ih : tail.toOrder.length = (peelSink R s).n := toOrder_length tail
    have hRn : (peelSink R s).n = R.n - 1 := rfl
    have hpos : 0 < R.n :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) s.isLt
    show (s :: tail.toOrder.map (embedSkip s)).length = R.n
    simp [List.length_cons, List.length_map, ih, hRn]
    omega

/-- The canonical descent order has no duplicate packet indices.
Each `cons` step's sink `s` cannot reappear in the tail (every
lifted tail index comes from `embedSkip s`, which never lands on
`s`), and lifted tail indices are mutually distinct because
`embedSkip s` is injective. -/
theorem toOrder_nodup :
    ∀ {R : CompletedReconstructionRecord setup} (c : PeelChain R),
      c.toOrder.Nodup
  | _, .nil _ _ => by simp [toOrder]
  | R, .cons _ s _ tail => by
    have ih : tail.toOrder.Nodup := toOrder_nodup tail
    have hmap : (tail.toOrder.map (embedSkip s)).Nodup :=
      List.Nodup.map (embedSkip_injective s) ih
    refine List.nodup_cons.mpr ⟨?_, hmap⟩
    intro hmem
    obtain ⟨i, _, heq⟩ := List.mem_map.mp hmem
    exact embedSkip_ne s i heq

/-- **The canonical reconstruction order in the original frame.**

For a completed reconstruction record `R`, this is the list of
original-frame packet indices `Fin R.n` produced by descending the
`canonicalPeelChain` and lifting each residual-frame sink choice
back through the iterated `embedSkip`. -/
noncomputable def canonicalPeelOrder
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    List (Fin R.n) :=
  (canonicalPeelChain R hC).toOrder

/-- **The canonical order has length `R.n`.** -/
theorem canonicalPeelOrder_length
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalPeelOrder R hC).length = R.n :=
  toOrder_length _

/-- **The canonical order has no duplicate packet indices.** -/
theorem canonicalPeelOrder_nodup
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalPeelOrder R hC).Nodup :=
  toOrder_nodup _

/-- **Head characterization (depth 0).** When `R.n > 0`, the first
element of the canonical order is the canonical sink of `R`. This
is the "each listed index corresponds to the canonical sink of the
appropriate residual stage" statement at depth 0. The general per-
stage statement (lifting depth-`k` sinks through the iterated
`embedSkip` cascade and matching them against the canonical sink
of `R_k`) follows by structural induction down the chain; only the
depth-0 head equation is recorded here as the headline corollary
of `IsCanonical` plus `toOrder`. -/
theorem canonicalPeelOrder_head?
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (hpos : 0 < R.n) :
    (canonicalPeelOrder R hC).head? = some (canonicalSink R hpos) := by
  -- Unfold one step of `canonicalPeelChainAux` to expose the cons.
  unfold canonicalPeelOrder canonicalPeelChain canonicalPeelChainAux
  have hzero : ¬ R.n = 0 := Nat.pos_iff_ne_zero.mp hpos
  simp only [hzero, dif_neg, not_false_eq_true]
  rfl

/-! ### Stagewise correctness of the canonical order (Phase 3A item 3 sub-item 3.5)

The previous sub-item gave the depth-0 anchor only. Here we expose
the **per-stage** machinery and prove the general stagewise
characterization:

  *for every depth `k < R.n`, the `k`-th element of
  `canonicalPeelOrder R hC` is the iterated-`embedSkip` lift of the
  canonical sink `canonicalSink R_k _` of the `k`-th residual `R_k`*.

The infrastructure introduced:

* `nthResidual c k hk : CompletedReconstructionRecord setup` — the
  depth-`k` residual record reached by descending the chain `k`
  steps.
* `nthRawSink c k hk : Fin (nthResidual c k _).n` — the depth-`k`
  cons-cell sink, in its **own** residual frame (no lift yet).
* `nthLiftedSink c k hk : Fin R.n` — the depth-`k` cons-cell sink
  lifted back to the **original** `R`'s frame, by iterating
  `embedSkip` through the first `k` cons cells.
* `nthLiftedSink_eq_toOrder_get` — the order *is* the lift sequence.
* `nthRawSink_eq_canonicalSink_of_isCanonical` — for an
  `IsCanonical` chain, the raw sink at depth `k` is exactly the
  canonical sink of the `k`-th residual.
* Headline `canonicalPeelOrder_get_stagewise` — combines the above
  into the user's stagewise statement.

**Scope (per user)**: this proves *order-stagewise alignment*; it
does **not** construct a canonical word, does **not** identify
`canonicalPeelOrder` with any reconstruction syntax, and does
**not** claim reconstruction uniqueness. Those are subsequent
sub-items. -/

/-- The depth-`k` residual record reached by descending the chain
`k` steps. For `k = 0` it is the starting record; each `cons` step
peels one packet via `peelSink`. -/
def nthResidual : ∀ {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (k : Nat), k ≤ c.length →
    CompletedReconstructionRecord setup
  | R, .nil _ _, _, _ => R
  | R, .cons _ _ _ _, 0, _ => R
  | _, .cons _ _ _ tail, k+1, hk =>
      nthResidual tail k (Nat.le_of_succ_le_succ hk)

/-- The depth-`k` cons-cell sink, expressed in its own residual
frame `Fin (nthResidual c k _).n`. This is the sink chosen at the
`k`-th `cons` cell of the chain, before any lifting. -/
def nthRawSink : ∀ {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (k : Nat) (hk : k < c.length),
    Fin (nthResidual c k (Nat.le_of_lt hk)).n
  | _, .nil _ _, _, hk => absurd hk (by simp [length])
  | _, .cons _ s _ _, 0, _ => s
  | _, .cons _ _ _ tail, k+1, hk =>
      tail.nthRawSink k (Nat.lt_of_succ_lt_succ hk)

/-- The depth-`k` cons-cell sink, lifted back to the **original**
`R`'s frame `Fin R.n` by iterating `embedSkip` through the first
`k` cons cells. -/
def nthLiftedSink : ∀ {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (k : Nat), k < c.length → Fin R.n
  | _, .nil _ _, _, hk => absurd hk (by simp [length])
  | _, .cons _ s _ _, 0, _ => s
  | _, .cons _ s _ tail, k+1, hk =>
      embedSkip s (tail.nthLiftedSink k (Nat.lt_of_succ_lt_succ hk))

/-- **Stagewise correctness of `toOrder` (general, choice-blind).**
For any peel chain `c`, the `k`-th element of `c.toOrder` is the
iterated-`embedSkip` lift of the `k`-th cons-cell sink. This holds
for arbitrary chains (not just canonical ones) and is the
structural backbone of the stagewise theorem. -/
theorem nthLiftedSink_eq_toOrder_get :
    ∀ {R : CompletedReconstructionRecord setup}
      (c : PeelChain R) (k : Nat) (hk : k < c.length),
      c.toOrder.get ⟨k, by rw [toOrder_length, ← length_eq c]; exact hk⟩
        = c.nthLiftedSink k hk
  | _, .nil _ _, _, hk => absurd hk (by simp [length])
  | _, .cons R s _ tail, 0, _ => by
      show ((s :: tail.toOrder.map (embedSkip s)).get ⟨0, _⟩) = s
      rfl
  | _, .cons R s _ tail, k+1, hk => by
      have hk' : k < tail.length := Nat.lt_of_succ_lt_succ hk
      have ih := nthLiftedSink_eq_toOrder_get tail k hk'
      show ((s :: tail.toOrder.map (embedSkip s)).get ⟨k+1, _⟩)
            = embedSkip s (tail.nthLiftedSink k hk')
      have hkmap : k < (tail.toOrder.map (embedSkip s)).length := by
        rw [List.length_map, toOrder_length]; rw [length_eq tail] at hk'; exact hk'
      rw [List.get_cons_succ]
      show (tail.toOrder.map (embedSkip s)).get ⟨k, hkmap⟩
            = embedSkip s (tail.nthLiftedSink k hk')
      simp only [List.get_eq_getElem, List.getElem_map]
      exact congrArg (embedSkip s) ih

/-- **Canonicality is per-cell-sink-by-depth.** For an `IsCanonical`
chain, the raw sink at depth `k` (in its own residual frame) is
exactly `canonicalSink` of the `k`-th residual. -/
theorem nthRawSink_eq_canonicalSink_of_isCanonical :
    ∀ {R : CompletedReconstructionRecord setup}
      (c : PeelChain R) (_hcan : IsCanonical c) (k : Nat) (hk : k < c.length),
      ∃ hpos : 0 < (nthResidual c k (Nat.le_of_lt hk)).n,
        c.nthRawSink k hk
          = canonicalSink (nthResidual c k (Nat.le_of_lt hk)) hpos
  | _, .nil _ _, _, _, hk => absurd hk (by simp [length])
  | R, .cons _ s _ tail, hcan, 0, hk => by
      -- depth 0: nthResidual = R, nthRawSink = s, IsCanonical's
      -- first conjunct gives s = canonicalSink R hpos.
      obtain ⟨⟨hpos, hs⟩, _⟩ := hcan
      refine ⟨hpos, ?_⟩
      show s = canonicalSink R hpos
      exact hs
  | _, .cons _ _ _ tail, hcan, k+1, hk => by
      have hcan' : IsCanonical tail := hcan.2
      have hk' : k < tail.length := Nat.lt_of_succ_lt_succ hk
      exact tail.nthRawSink_eq_canonicalSink_of_isCanonical hcan' k hk'

/-- **Headline (stagewise correctness of `canonicalPeelOrder`).**

For every depth `k < R.n`, the `k`-th element of
`canonicalPeelOrder R hC` is the iterated-`embedSkip` lift of the
canonical sink of the `k`-th residual record. This is the
"each listed index corresponds to the canonical sink of the
appropriate residual stage" statement at general depth `k`,
generalising `canonicalPeelOrder_head?` (which only handled `k = 0`).

**The canonical order is the original-frame shadow of the canonical
peel chain.** -/
theorem canonicalPeelOrder_get_stagewise
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (k : Nat) (hk : k < R.n) :
    (canonicalPeelOrder R hC).get
        ⟨k, by rw [canonicalPeelOrder_length]; exact hk⟩
      = (canonicalPeelChain R hC).nthLiftedSink k
          (by rw [length_eq]; exact hk) := by
  exact nthLiftedSink_eq_toOrder_get
          (canonicalPeelChain R hC) k (by rw [length_eq]; exact hk)

/-- **Per-stage canonical-sink characterization.** For every depth
`k < R.n`, the `k`-th raw sink of the canonical peel chain is
`canonicalSink` of the `k`-th residual. Combined with
`canonicalPeelOrder_get_stagewise` and the structural definition of
`nthLiftedSink`, this gives the full per-stage equation
`canonicalPeelOrder R hC[k] = (iterated embedSkip)(canonicalSink R_k _)`. -/
theorem canonicalPeelOrder_nthRawSink_canonical
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (k : Nat) (hk : k < R.n) :
    let c := canonicalPeelChain R hC
    let hk' : k < c.length := by show k < c.length; rw [length_eq]; exact hk
    ∃ hpos : 0 < (c.nthResidual k (Nat.le_of_lt hk')).n,
      c.nthRawSink k hk'
        = canonicalSink (c.nthResidual k (Nat.le_of_lt hk')) hpos := by
  exact nthRawSink_eq_canonicalSink_of_isCanonical
          (canonicalPeelChain R hC)
          (canonicalPeelChain_isCanonical R hC) k _

/-! ### Canonical reconstruction word (Phase 3A item 3 sub-item 4)

Having stagewise correctness of `canonicalPeelOrder`, we can now
build the **canonical reconstruction word** by attaching to each
listed packet index its actual `Packet` data from `R.packets`. The
word is a `List` of `WordEntry R`; each entry pairs an
original-frame index `i : Fin R.n` with the packet `R.packets i`.

**Scope of this sub-item (per user)**:
* The word is *built from* `canonicalPeelOrder`, not from a
  re-selection of sinks — concretely, `canonicalWord R hC :=
  (canonicalPeelOrder R hC).map (fun i => ⟨i, R.packets i⟩)`.
* We prove length, packet-index projection equality, `Nodup` of
  the projection, and stagewise correctness (the `k`-th word
  entry's index is `nthLiftedSink k _` of the canonical chain).
* We do **not** define replay semantics here, do **not** claim the
  word "replays correctly" against the manuscript's
  `def:replay-representative` (that requires the cycle-4 replay
  infrastructure to be threaded through), and do **not** claim
  reconstruction uniqueness.

**Vocabulary discipline**: this is an *intrinsic* word in the
mathematical sense (built deterministically from `R` and `hC` via
`canonicalSink`-driven descent); it is the source of the canonical
*replay word* once replay semantics are bridged in. -/

/-- A single entry of the canonical reconstruction word: an
original-frame packet index together with its packet data. The
packet field is the packet that lives at `packetIndex` in the
original record `R` (i.e. `R.packets packetIndex`). -/
structure WordEntry (R : CompletedReconstructionRecord setup) where
  /-- The original-frame index of the packet to be reconstructed
  at this word position. -/
  packetIndex : Fin R.n
  /-- The packet itself, expected to equal `R.packets packetIndex`
  (enforced by the construction `canonicalWord`; the structure does
  not impose this as a field-level invariant). -/
  packet : Packet setup

/-- **The canonical reconstruction word.** Built by attaching to
each index in `canonicalPeelOrder R hC` the packet at that index
in the original record. The word is intrinsic to `R` and `hC`
because `canonicalPeelOrder` is. -/
noncomputable def canonicalWord
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    List (WordEntry R) :=
  (canonicalPeelOrder R hC).map (fun i => ⟨i, R.packets i⟩)

/-- **Length of the canonical word.** Equal to `R.n`. -/
theorem canonicalWord_length
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalWord R hC).length = R.n := by
  simp [canonicalWord, List.length_map, canonicalPeelOrder_length]

/-- **Packet-index projection of the canonical word equals the
canonical peel order.** -/
theorem canonicalWord_packetIndex_eq_order
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalWord R hC).map WordEntry.packetIndex
      = canonicalPeelOrder R hC := by
  show (List.map WordEntry.packetIndex
          ((canonicalPeelOrder R hC).map (fun i => ⟨i, R.packets i⟩)))
        = canonicalPeelOrder R hC
  rw [List.map_map]
  show (canonicalPeelOrder R hC).map
          (WordEntry.packetIndex ∘ (fun i : Fin R.n => ⟨i, R.packets i⟩))
        = canonicalPeelOrder R hC
  have : (WordEntry.packetIndex ∘ (fun i : Fin R.n => (⟨i, R.packets i⟩ : WordEntry R)))
          = id := by funext i; rfl
  rw [this, List.map_id]

/-- **Packet-index list of the canonical word has no duplicates.**
Inherited from `canonicalPeelOrder_nodup` via the projection
equality. -/
theorem canonicalWord_packetIndex_nodup
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    ((canonicalWord R hC).map WordEntry.packetIndex).Nodup := by
  rw [canonicalWord_packetIndex_eq_order]
  exact canonicalPeelOrder_nodup R hC

/-- **Per-entry packet-data correctness.** Each entry's `packet`
field equals `R.packets` applied to the entry's `packetIndex`.
This is by construction of `canonicalWord`, but is recorded
explicitly because downstream consumers (replay semantics) will
need it. -/
theorem canonicalWord_packet_eq
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (e : WordEntry R) (he : e ∈ canonicalWord R hC) :
    e.packet = R.packets e.packetIndex := by
  simp only [canonicalWord, List.mem_map] at he
  obtain ⟨i, _, heq⟩ := he
  rw [← heq]

/-- **Stagewise correctness of the canonical word.** For every
depth `k < R.n`, the `k`-th word entry's `packetIndex` equals the
`k`-th lifted canonical sink of the canonical peel chain — i.e.
the iterated-`embedSkip` lift of `canonicalSink` of the `k`-th
residual. This packages
`canonicalPeelOrder_get_stagewise` through the projection
`WordEntry.packetIndex`. -/
theorem canonicalWord_get_packetIndex_stagewise
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (k : Nat) (hk : k < R.n) :
    ((canonicalWord R hC).get
        ⟨k, by rw [canonicalWord_length]; exact hk⟩).packetIndex
      = (canonicalPeelChain R hC).nthLiftedSink k
          (by rw [length_eq]; exact hk) := by
  -- Both sides reduce: LHS via `getElem_map` to `(canonicalPeelOrder).get k`,
  -- which equals RHS by `canonicalPeelOrder_get_stagewise`.
  have hstage := canonicalPeelOrder_get_stagewise R hC k hk
  unfold canonicalWord
  simp only [List.get_eq_getElem, List.getElem_map]
  exact hstage

/-! ### Coverage / permutation properties of the canonical reconstruction
(Phase 3A item 3 sub-item 5).

These are the structural correctness facts about the canonical word
that hold *prior to* any replay semantics: every original packet index
is enumerated exactly once. -/

/-- **Coverage of the canonical peel order.** Every packet index of
the original record appears in `canonicalPeelOrder R hC`.

Proof: the order has length `R.n` and is `Nodup`, so its `toFinset`
has cardinality `R.n = Fintype.card (Fin R.n)`, hence equals
`Finset.univ`; membership in the underlying list is membership in
the finset. -/
theorem canonicalPeelOrder_mem
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (i : Fin R.n) : i ∈ canonicalPeelOrder R hC := by
  classical
  -- Convert membership to membership in `toFinset` then leverage cardinality.
  have hnodup : (canonicalPeelOrder R hC).Nodup := canonicalPeelOrder_nodup R hC
  have hlen : (canonicalPeelOrder R hC).length = R.n := canonicalPeelOrder_length R hC
  have hcard : (canonicalPeelOrder R hC).toFinset.card = R.n := by
    rw [List.toFinset_card_of_nodup hnodup, hlen]
  have huniv : (canonicalPeelOrder R hC).toFinset = (Finset.univ : Finset (Fin R.n)) := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  have : i ∈ (canonicalPeelOrder R hC).toFinset := by
    rw [huniv]; exact Finset.mem_univ i
  simpa [List.mem_toFinset] using this

/-- **The canonical peel order, as a finset, is everything.** -/
theorem canonicalPeelOrder_toFinset_eq_univ
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalPeelOrder R hC).toFinset = (Finset.univ : Finset (Fin R.n)) := by
  classical
  apply Finset.eq_univ_of_card
  rw [List.toFinset_card_of_nodup (canonicalPeelOrder_nodup R hC),
      canonicalPeelOrder_length, Fintype.card_fin]

/-- **Coverage of the canonical word.** Every packet index `i : Fin R.n`
is the `packetIndex` of some entry in `canonicalWord R hC`. -/
theorem canonicalWord_packetIndex_mem
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (i : Fin R.n) :
    ∃ e ∈ canonicalWord R hC, e.packetIndex = i := by
  -- The projection list contains `i`, so the underlying list contains a
  -- corresponding entry.
  have hi : i ∈ (canonicalWord R hC).map WordEntry.packetIndex := by
    rw [canonicalWord_packetIndex_eq_order]
    exact canonicalPeelOrder_mem R hC i
  rcases List.mem_map.1 hi with ⟨e, he, hproj⟩
  exact ⟨e, he, hproj⟩

/-- **Uniqueness of the entry covering each packet index.** Combined
with `canonicalWord_packetIndex_mem`, this says every original packet
index is the `packetIndex` of *exactly one* entry of the canonical
word. -/
theorem canonicalWord_packetIndex_unique
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    {e₁ e₂ : WordEntry R}
    (h₁ : e₁ ∈ canonicalWord R hC) (h₂ : e₂ ∈ canonicalWord R hC)
    (hidx : e₁.packetIndex = e₂.packetIndex) : e₁ = e₂ := by
  -- Both entries' packets are determined by their (equal) packetIndex.
  have hp₁ := canonicalWord_packet_eq R hC e₁ h₁
  have hp₂ := canonicalWord_packet_eq R hC e₂ h₂
  cases e₁ with
  | mk i₁ p₁ =>
    cases e₂ with
    | mk i₂ p₂ =>
      simp only at hidx
      subst hidx
      simp only at hp₁ hp₂
      subst hp₁
      subst hp₂
      rfl

/-- **The canonical peel order is a permutation of `Finset.univ`'s
underlying enumeration.** Phrased through `toFinset` equality + Nodup
+ length: the order enumerates every `Fin R.n` exactly once. -/
theorem canonicalPeelOrder_isEnumeration
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted) :
    (canonicalPeelOrder R hC).Nodup
      ∧ (canonicalPeelOrder R hC).length = R.n
      ∧ ∀ i : Fin R.n, i ∈ canonicalPeelOrder R hC :=
  ⟨canonicalPeelOrder_nodup R hC,
   canonicalPeelOrder_length R hC,
   canonicalPeelOrder_mem R hC⟩

/-! ### Uniqueness of the canonical descent (Phase 3A item 3 sub-item 6).

The canonical chain is uniquely determined by `R` and `hC` *as data*:
any peel chain on `R` that is simultaneously `Completes` and
`IsCanonical` produces the same `toOrder`, and hence the same
`canonicalWord`, as `canonicalPeelChain R hC`.

This is the strongest uniqueness statement available **without
replay semantics**: it expresses that canonicality (= "at every
depth, the sink is `canonicalSink`") forces the entire enumeration
in the original frame. It does **not** assert chain-level equality
(`c = canonicalPeelChain R hC` would require dependent-type
reasoning across `R.IsCompleted`-witness propagation that is heavier
than needed downstream); the `toOrder`/word-level equality suffices
for any consumer that only reads off the order or the word. -/

/-- The first conjunct of `Completes`. -/
theorem completes_head : ∀ {R : CompletedReconstructionRecord setup}
    {c : PeelChain R}, Completes c → R.IsCompleted
  | _, .nil _ _, hC => hC
  | _, .cons _ _ _ _, hC => hC.1

/-- Reduction of `canonicalPeelChain` in the `R.n = 0` branch. -/
theorem canonicalPeelChain_zero
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (h : R.n = 0) :
    canonicalPeelChain R hC = PeelChain.nil R h := by
  unfold canonicalPeelChain canonicalPeelChainAux
  rw [dif_pos h]

/-- Reduction of `canonicalPeelChain` in the `0 < R.n` branch. -/
theorem canonicalPeelChain_pos
    (R : CompletedReconstructionRecord setup) (hC : R.IsCompleted)
    (hpos : 0 < R.n) :
    canonicalPeelChain R hC
      = PeelChain.cons R (canonicalSink R hpos)
          (canonicalSink_isSink R hpos)
          (canonicalPeelChain (peelSink R (canonicalSink R hpos))
            (sink_peel_preserves_completedness
              (canonicalSink_isSink R hpos) hC)) := by
  -- Unfold both `canonicalPeelChain` and `canonicalPeelChainAux`,
  -- discharge the `if`-branch via `Nat.pos_iff_ne_zero`.
  show (canonicalPeelChainAux R hC).1 = _
  conv_lhs => rw [canonicalPeelChainAux]
  rw [dif_neg (Nat.pos_iff_ne_zero.mp hpos)]
  rfl

/-- **Uniqueness of `toOrder` along any canonical completing chain.**
For every chain `c : PeelChain R` that is simultaneously `Completes`
and `IsCanonical`, the original-frame order it produces equals the
canonical peel order extracted from `R`. -/
theorem toOrder_eq_canonicalPeelOrder_of_isCanonical
    {R : CompletedReconstructionRecord setup} (c : PeelChain R) :
    ∀ (hCo : Completes c) (_hCan : IsCanonical c),
      c.toOrder = canonicalPeelOrder R (completes_head hCo) := by
  induction c with
  | nil R h =>
    intro hCo _hCan
    have hC : R.IsCompleted := completes_head hCo
    show ([] : List (Fin R.n)) = canonicalPeelOrder R hC
    unfold canonicalPeelOrder
    rw [canonicalPeelChain_zero R hC h]
    rfl
  | cons R s hSink tail ih =>
    intro hCo hCan
    have hC : R.IsCompleted := completes_head hCo
    have hCo_tail : Completes tail := hCo.2
    have hCan_tail : IsCanonical tail := hCan.2
    obtain ⟨hpos, hseq⟩ := hCan.1
    -- Tail order matches canonical order on residual.
    have ihtail :
        tail.toOrder
          = canonicalPeelOrder (peelSink R s) (completes_head hCo_tail) :=
      ih hCo_tail hCan_tail
    -- Eliminate `s` in favor of `canonicalSink R hpos` in all dependent
    -- positions (including `tail`'s type and `ihtail`'s residual record).
    subst hseq
    -- The goal now has `canonicalSink R hpos` everywhere `s` was.
    show (canonicalSink R hpos
          :: tail.toOrder.map (embedSkip (canonicalSink R hpos)))
        = canonicalPeelOrder R hC
    unfold canonicalPeelOrder
    rw [canonicalPeelChain_pos R hC hpos]
    -- RHS toOrder unfolds to `canonicalSink R hpos :: (residual canonical chain).toOrder.map (embedSkip ...)`.
    show _ = canonicalSink R hpos
              :: (canonicalPeelChain
                    (peelSink R (canonicalSink R hpos))
                    (sink_peel_preserves_completedness
                      (canonicalSink_isSink R hpos) hC)).toOrder.map
                (embedSkip (canonicalSink R hpos))
    congr 1
    -- Inner equality follows from `ihtail` (now stated on the residual
    -- record `peelSink R (canonicalSink R hpos)`); both `canonicalPeelOrder`
    -- invocations carry IsCompleted witnesses for the same Prop, so the
    -- underlying canonical chain is the same.
    exact congrArg (List.map _) ihtail

/-- **Uniqueness of `canonicalPeelOrder` from canonicality.** Direct
corollary: any completing canonical chain has the canonical peel
order. -/
theorem canonicalPeelOrder_eq_toOrder_of_isCanonical
    {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (hCo : Completes c) (hCan : IsCanonical c) :
    canonicalPeelOrder R (completes_head hCo) = c.toOrder :=
  (toOrder_eq_canonicalPeelOrder_of_isCanonical c hCo hCan).symm

/-- **Uniqueness of the canonical word from canonicality.** For any
chain that is both completing and canonical, the canonical word
attached to that chain's `toOrder` equals `canonicalWord R hC`. -/
theorem canonicalWord_eq_of_isCanonical
    {R : CompletedReconstructionRecord setup}
    (c : PeelChain R) (hCo : Completes c) (hCan : IsCanonical c) :
    (c.toOrder).map (fun i => (⟨i, R.packets i⟩ : WordEntry R))
      = canonicalWord R (completes_head hCo) := by
  unfold canonicalWord
  rw [toOrder_eq_canonicalPeelOrder_of_isCanonical c hCo hCan]

end PeelChain

/-
TEX ref: our_paper_draft.tex, label prop:reconstruction-termination (L1165+)
Paper role: the canonical reconstruction algorithm terminates; proved by
  well-founded induction on R.n (the number of packets), which strictly
  decreases at each sink-peel step
Lean status: MISSING → stub added (M2)
-/
/-- **`prop:reconstruction-termination`**: the canonical reconstruction algorithm
terminates on every completed record.

The algorithm recurses on `peelSink R (canonicalSink R hpos)`, which has
`n - 1` packets when `R` has `n`. Termination follows from well-founded induction
on `R.n`. The chain `canonicalPeelChain R hC` is already constructed by structural
recursion on `R.n` in this file; this proposition records the manuscript's formal
termination statement. -/
theorem reconstruction_termination
    {setup : RewriteCalculusSetup.{u}}
    (R : CompletedReconstructionRecord setup)
    (hC : R.IsCompleted) :
    ∃ (c : PeelChain R), c.Completes :=
  ⟨PeelChain.canonicalPeelChain R hC, PeelChain.canonicalPeelChain_completes R hC⟩

/-
TEX ref: our_paper_draft.tex, label prop:reconstruction-existence (L1172+)
Paper role: for every completed reconstruction record there exists a canonical
  completed trace; the algorithm produces such a trace
Lean status: MISSING → stub added (M2)
-/
/-- **`prop:reconstruction-existence`**: every completed reconstruction record
admits a canonical peel-chain reconstruction.

The existence is witnessed by `canonicalPeelChain R hC` together with its
completing proof. This records the manuscript's existence clause as a named
proposition. -/
theorem reconstruction_existence
    {setup : RewriteCalculusSetup.{u}}
    (R : CompletedReconstructionRecord setup)
    (hC : R.IsCompleted) :
    ∃ (c : PeelChain R), c.Completes ∧ c.IsCanonical :=
  ⟨PeelChain.canonicalPeelChain R hC,
   PeelChain.canonicalPeelChain_completes R hC,
   PeelChain.canonicalPeelChain_isCanonical R hC⟩

end CompletedReconstructionRecord
end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
