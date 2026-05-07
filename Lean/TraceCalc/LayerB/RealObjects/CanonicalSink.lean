import TraceCalc.LayerB.RealObjects.SinkExists
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.MinMax

/-!
# Real-objects formalization: the canonical sink

**Real-objects path, Phase 3A item 1 (2026-04-23).**

This file discharges the second half of `our_paper_draft.tex` L1184:

> *"the canonical sink is the `Key`-greatest sink"*

That sentence is a constructive recipe: among all sinks of the
dependence DAG (existence of which is `DepGraph.sink_exists` from
[Lean/TraceCalc/LayerB/RealObjects/SinkExists.lean](Lean/TraceCalc/LayerB/RealObjects/SinkExists.lean)),
pick the one whose canonical-key position is largest. Uniqueness is
immediate from `CanonicalKey.total` (injectivity of `pos`).

## What this file contains

* `CompletedReconstructionRecord.canonicalSink` — the `Key`-greatest
  sink of a completed reconstruction record with at least one packet.
* `canonicalSink_isSink` — it is in fact a sink.
* `canonicalSink_pos_max` — its key-position dominates the
  key-positions of every other sink.
* `canonicalSink_unique` — any sink whose key-position equals the
  canonical sink's key-position is the canonical sink (immediate from
  `key.total`'s injectivity).

The construction is a finite search over `List.finRange R.n`: we score
each index by `0` when it is not a sink and by `pos + 1` when it is a
sink, then use `List.argmax` to choose a maximizer. No `Classical.choice`
is needed in the implementation.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

/-- `DepGraph.IsSink s` is decidable: `∀ j : Fin n, edge s j = false` is
a finite conjunction of `Bool`-equality checks. Required for
`Finset.filter`-based constructions below. -/
instance DepGraph.IsSink.instDecidable {n : Nat} (G : DepGraph n)
    (s : Fin n) : Decidable (G.IsSink s) := by
  unfold DepGraph.IsSink; infer_instance

namespace CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-- The finite set of sinks of a completed reconstruction record's
dependence DAG. -/
def sinksFinset (R : CompletedReconstructionRecord setup) :
    Finset (Fin R.n) :=
  Finset.univ.filter R.dep.IsSink

/-- The set of sinks is nonempty whenever the record has at least one
packet. Combines `DepGraph.sink_exists` (cycle 7) with the membership
characterization of `sinksFinset`. -/
lemma sinksFinset_nonempty (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) : (sinksFinset R).Nonempty := by
  obtain ⟨s, hs⟩ := R.dep.sink_exists hpos
  refine ⟨s, ?_⟩
  simp [sinksFinset, hs]

lemma mem_sinksFinset {R : CompletedReconstructionRecord setup}
    {s : Fin R.n} : s ∈ sinksFinset R ↔ R.dep.IsSink s := by
  simp [sinksFinset]

/-- The image of the sink set under the canonical key's position
function. By `R.key.total` (injectivity of `pos`), this image
faithfully represents the set of sinks. -/
def sinkPositions (R : CompletedReconstructionRecord setup) :
    Finset (Fin R.n) :=
  (sinksFinset R).image R.key.pos

lemma sinkPositions_nonempty (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) : (sinkPositions R).Nonempty :=
  (sinksFinset_nonempty R hpos).image _

/-! ### The canonical sink

L1184: *"the canonical sink is the `Key`-greatest sink."* The maximum
is taken in the underlying `LinearOrder` of `Fin R.n`; for the canonical
key this *is* the manuscript's "greatest" because `R.key.pos` lands in
`Fin R.n` and the manuscript's "greater" means "later in the canonical
ordering" — i.e., larger `pos`. -/

/-- Score used by the executable canonical sink search: sinks are ranked by
their canonical-key positions, and non-sinks are ranked below every sink. -/
private def sinkScore (R : CompletedReconstructionRecord setup)
    (s : Fin R.n) : Nat :=
  if R.dep.IsSink s then (R.key.pos s).1 + 1 else 0

/-- The `argmax` search over `finRange` is nonempty when `R.n > 0`. -/
private lemma canonicalSink_argmax_isSome
    (R : CompletedReconstructionRecord setup) (hpos : 0 < R.n) :
    (List.argmax (sinkScore R) (List.finRange R.n)).isSome := by
  cases harg : List.argmax (sinkScore R) (List.finRange R.n) with
  | none =>
      have hnzero : R.n = 0 :=
        List.finRange_eq_nil.mp (List.argmax_eq_none.mp harg)
      exact False.elim (Nat.ne_of_gt hpos hnzero)
  | some s =>
      simp [harg]

/-- **The canonical sink** (`our_paper_draft.tex` L1184): the unique
sink whose canonical-key position is maximal among all sinks. -/
def canonicalSink (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) : Fin R.n :=
  Option.get _ (canonicalSink_argmax_isSome R hpos)

/-- The canonical sink is, in fact, a sink. -/
theorem canonicalSink_isSink (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) : R.IsSink (canonicalSink R hpos) := by
  obtain ⟨s, hs⟩ := R.dep.sink_exists hpos
  have harg_mem :
      canonicalSink R hpos ∈ List.argmax (sinkScore R) (List.finRange R.n) := by
    unfold canonicalSink
    exact Option.get_mem (canonicalSink_argmax_isSome R hpos)
  have hmax :
      sinkScore R s ≤ sinkScore R (canonicalSink R hpos) :=
    List.le_of_mem_argmax (f := sinkScore R) (List.mem_finRange s) harg_mem
  by_cases hsel : R.dep.IsSink (canonicalSink R hpos)
  · simpa using hsel
  · simp [sinkScore, hs, hsel] at hmax

/-- The canonical sink's key-position dominates the key-position of
every other sink. This is the manuscript's "`Key`-greatest" property
(L1184). -/
theorem canonicalSink_pos_max (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) {s : Fin R.n} (hs : R.IsSink s) :
    R.key.pos s ≤ R.key.pos (canonicalSink R hpos) := by
  have hs' : R.dep.IsSink s := by
    simpa using hs
  have hsel : R.dep.IsSink (canonicalSink R hpos) := by
    simpa using canonicalSink_isSink R hpos
  have harg_mem :
      canonicalSink R hpos ∈ List.argmax (sinkScore R) (List.finRange R.n) := by
    unfold canonicalSink
    exact Option.get_mem (canonicalSink_argmax_isSome R hpos)
  have hmax :
      sinkScore R s ≤ sinkScore R (canonicalSink R hpos) :=
    List.le_of_mem_argmax (f := sinkScore R) (List.mem_finRange s) harg_mem
  have hmax_nat : (R.key.pos s).1 + 1 ≤ (R.key.pos (canonicalSink R hpos)).1 + 1 := by
    simpa [sinkScore, hs', hsel] using hmax
  simpa using (Nat.succ_le_succ_iff.mp hmax_nat)

/-- **Uniqueness of the canonical sink.** Any sink whose key-position
equals the canonical sink's key-position must be the canonical sink
itself. Immediate from `R.key.total` (injectivity of `pos`). -/
theorem canonicalSink_unique (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) {s : Fin R.n} (_hs : R.IsSink s)
    (hpos_eq : R.key.pos s = R.key.pos (canonicalSink R hpos)) :
    s = canonicalSink R hpos :=
  R.key.total hpos_eq

/-- A convenient equational corollary: if `s` is a sink with maximal
key-position among all sinks, then `s` *is* the canonical sink. This is
the manuscript's intended characterization (L1184) made into a usable
unfolding lemma for downstream proofs. -/
theorem canonicalSink_eq_of_max (R : CompletedReconstructionRecord setup)
    (hpos : 0 < R.n) {s : Fin R.n} (hs : R.IsSink s)
    (hmax : ∀ t : Fin R.n, R.IsSink t → R.key.pos t ≤ R.key.pos s) :
    s = canonicalSink R hpos := by
  have h₁ : R.key.pos s ≤ R.key.pos (canonicalSink R hpos) :=
    canonicalSink_pos_max R hpos hs
  have h₂ : R.key.pos (canonicalSink R hpos) ≤ R.key.pos s :=
    hmax _ (canonicalSink_isSink R hpos)
  exact canonicalSink_unique R hpos hs (le_antisymm h₁ h₂)

end CompletedReconstructionRecord
end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
