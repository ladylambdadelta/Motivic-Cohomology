import TraceCalc.LayerB.RealObjects.Replay

/-!
# Real-objects formalization: independent sinks and sink-preservation under peeling

**Phase 3B item 5d (2026-04-24, first installment).** Per user's
verbatim Phase 3B item 5d directive: "do not begin with quotients.
First define the minimal `IndependentSinks` predicate and prove a
two-step peel commutation theorem: peeling independent sinks in either
order yields RecordEquiv records. Only then wrap this as an
adjacent-swap administrative move on `PeelChain`."

This file delivers the **first installment**: the `IndependentSinks`
predicate plus the *sink-preservation* half — that the index of `t`
in the peeled record `peelSink R s` (when `t ≠ s` and `t` is a sink
of `R`) remains a sink. This is the type-level scaffolding without
which the swap-square cannot even be **stated**: peeling `t` out of
`peelSink R s` requires a witness that `t-after-s` is a sink there.

The full swap-square `peelSink_swap_recordEquiv` (item 5e) has a real
manuscript-level obstruction: `restrictedY` and `restrictedExternalOut`
involve port-list concatenation `(++)` which is **non-commutative**,
so `RecordEquiv.Y_eq` and `RecordEquiv.externalOut_eq` are not
provable at the abstract `RewriteCalculusSetup` level without either
(a) an extra setup-level commutativity axiom on
`exposeBoundaryUnderSinkDeletion`, or (b) a weaker structural
equivalence relation (`StructEquiv`) that drops the `Y`/`externalOut`
conjuncts. The honest path is to introduce `StructEquiv` in item 5e;
this file scopes only the pre-square scaffolding.

## Architecture

* `IndependentSinks R s t` — predicate (per user's verbatim shape):
  `s_ne_t`, `no_s_to_t`, `no_t_to_s`.
* `peelSinkOtherIdx s t hne : Fin (peelSink R s).n` — index of `t`
  in the peeled record, constructed directly without `Fin.cast`.
* `embedSkip_peelSinkOtherIdx` — round-trip lemma.
* `peelSinkOtherIdx_isSink` — sink-preservation.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause requires that any two valid recursive descents arrive at the
  same completed reconstruction; this in turn requires that adjacent
  independent-sink choices commute.
* L1186–L1192 — the per-step descent whose commutation under
  independent-sink permutation is the canonicality content.
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### `IndependentSinks` predicate -/

/-- Two indices `s, t : Fin R.n` are **independent sinks** when they
are distinct and neither has a dependence edge to the other.

Note: this predicate does *not* assert that `s` or `t` is a sink in
`R`; sinkness is supplied as a separate hypothesis at use sites.
However, when both *are* sinks of `R`, the `no_s_to_t` and `no_t_to_s`
clauses follow automatically from `R.IsSink s`/`R.IsSink t`. -/
structure IndependentSinks (R : CompletedReconstructionRecord setup)
    (s t : Fin R.n) : Prop where
  /-- Distinctness of the two indices. -/
  s_ne_t : s ≠ t
  /-- No dependence edge from `s` to `t`. -/
  no_s_to_t : R.dep.edge s t = false
  /-- No dependence edge from `t` to `s`. -/
  no_t_to_s : R.dep.edge t s = false

namespace IndependentSinks

/-- When both `s` and `t` are sinks of `R`, they are automatically
independent (provided `s ≠ t`). -/
theorem of_both_sinks {R : CompletedReconstructionRecord setup}
    {s t : Fin R.n} (hne : s ≠ t)
    (hSinkS : R.IsSink s) (hSinkT : R.IsSink t) :
    IndependentSinks R s t :=
  { s_ne_t := hne
    no_s_to_t := hSinkS t
    no_t_to_s := hSinkT s }

/-- Symmetry of `IndependentSinks`. -/
theorem symm {R : CompletedReconstructionRecord setup}
    {s t : Fin R.n} (h : IndependentSinks R s t) :
    IndependentSinks R t s :=
  { s_ne_t := fun heq => h.s_ne_t heq.symm
    no_s_to_t := h.no_t_to_s
    no_t_to_s := h.no_s_to_t }

end IndependentSinks

/-! ### Index of the other sink in the peeled record -/

/-- The index of `t` in the peeled record `peelSink R s`, when `t ≠ s`.

Direct construction without `Fin.cast`: if `t.val < s.val`, the index
in `Fin (R.n - 1)` is `t.val`; otherwise (so `s.val < t.val`) it is
`t.val - 1`. -/
def peelSinkOtherIdx {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : t ≠ s) : Fin (peelSink R s).n :=
  if h : t.val < s.val then
    ⟨t.val, by
      show t.val < R.n - 1
      have := s.isLt
      omega⟩
  else
    have hgt : s.val < t.val := by
      rcases Nat.lt_or_ge s.val t.val with hlt | hle
      · exact hlt
      · exact absurd (Fin.ext (show t.val = s.val by omega)) hne
    ⟨t.val - 1, by
      show t.val - 1 < R.n - 1
      have := t.isLt
      omega⟩

/-- `embedSkip` recovers the original `t` from `peelSinkOtherIdx`. -/
theorem embedSkip_peelSinkOtherIdx {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : t ≠ s) :
    embedSkip s (peelSinkOtherIdx s t hne) = t := by
  apply Fin.ext
  unfold peelSinkOtherIdx
  by_cases hlt : t.val < s.val
  · rw [dif_pos hlt]
    rw [embedSkip_lt s _ (by show t.val < s.val; exact hlt)]
  · rw [dif_neg hlt]
    have hgt : s.val < t.val := by
      rcases Nat.lt_or_ge s.val t.val with h' | h'
      · exact h'
      · exact absurd (Fin.ext (show t.val = s.val by omega)) hne
    rw [embedSkip_ge s _ (by
      show ¬ (t.val - 1) < s.val
      omega)]
    show t.val - 1 + 1 = t.val
    omega

/-! ### Sink-preservation -/

/-- **Sink-preservation under peeling.** If `t` is a sink of `R` and
`t ≠ s`, then the index `peelSinkOtherIdx s t hne` is a sink of
`peelSink R s`.

This is the type-level scaffolding for the eventual swap-square: it
provides the `IsSink` witness needed to peel `t` out of `peelSink R s`
in the first place. Together with the symmetric statement (peeling
`s` out of `peelSink R t`), this lets us **state** the swap-square
without yet proving its commutation. -/
theorem peelSinkOtherIdx_isSink {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : t ≠ s) (htSink : R.IsSink t) :
    (peelSink R s).IsSink (peelSinkOtherIdx s t hne) := by
  intro j
  -- Unfold (peelSink R s).IsSink to the restrictedDep edge predicate.
  show (peelSink R s).dep.edge (peelSinkOtherIdx s t hne) j = false
  show R.dep.edge
        (embedSkip s (peelSinkOtherIdx s t hne)) (embedSkip s j) = false
  rw [embedSkip_peelSinkOtherIdx]
  exact htSink (embedSkip s j)

/-- Sink-preservation **under independence**: a packaged form of
`peelSinkOtherIdx_isSink` consuming the full `IndependentSinks`
predicate plus the `R.IsSink t` hypothesis (the predicate alone is
not enough — `IndependentSinks` only requires absence of edges between
`s` and `t`, not that `t` is a sink in `R`). -/
theorem peelSinkOtherIdx_isSink_of_independent
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t) (htSink : R.IsSink t) :
    (peelSink R s).IsSink (peelSinkOtherIdx s t (fun heq => h.s_ne_t heq.symm)) :=
  peelSinkOtherIdx_isSink s t (fun heq => h.s_ne_t heq.symm) htSink

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
