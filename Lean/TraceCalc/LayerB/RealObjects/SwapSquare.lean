import TraceCalc.LayerB.RealObjects.IndependentPeel
import TraceCalc.LayerB.RealObjects.StructEquiv

/-!
# Real-objects formalization: independent-sink swap square (local generator)

**Phase 3B item 5e second installment (2026-04-24).** Per user's
verbatim 5e installment-2 directive: "keep `BoundaryTwoStepSwap` as a
**local generating relation only**. Do not force it to be reflexive
or transitive. First prove `peelSink_swap_structEquiv` with
`BR := BoundaryTwoStepSwap`. After that, introduce `BoundaryAdminEquiv`
as the closure used for global administrative chain equivalence."

This delivers exactly that: the **narrow local generator** plus the
swap-square theorem, then a separate inductive **closure** for global
administrative use. Per `INV StructEquiv-BoundaryParam`, the swap
theorem instantiates `BR` to the narrowest honest predicate for its
proof obligation; we never lift commutativity to a setup-level field.

## Architecture

* `embedSkip_swap` — the key index-commutation lemma: skipping `s`
  then `t-after-s` and skipping `t` then `s-after-t` agree as maps
  `Fin (R.n - 2) → Fin R.n`. Direct case analysis on `s.val` vs
  `t.val` and the relative position of `i.val`.
* `BoundaryTwoStepSwap h` — the **local generating relation** with
  exactly one constructor `.swap` relating the two literal `.Y`
  fields produced by deleting `s, t` in opposite orders. Tautological
  as a relation; its purpose is to **label** which boundary objects
  are equivalent under one independent-sink swap.
* `peelSink_swap_structEquiv` — the headline: for independent sinks
  `s, t`, the two two-step peelings are `RecordStructEquiv` along
  `BR := BoundaryTwoStepSwap h`, with `externalOut_perm` discharged
  by `(L ++ A) ++ B ~ (L ++ B) ++ A`.
* `BoundaryAdminEquiv` — the inductive closure: `refl`, `symm`,
  `trans`, plus `ofTwoStepSwap` lifting any `BoundaryTwoStepSwap`.
  This is the right `BR` for downstream global canonicality.
* `BoundaryAdminEquiv.refl`/`.symm`/`.trans` — equivalence-relation API
  derived from the constructors, suitable for plugging into
  `RecordStructEquiv.refl`/`.symm`/`.trans`.

## Manuscript anchor

`our_paper_draft.tex`:
* L1180 (`thm:canonical-reconstruction-algorithm`) — the canonicality
  clause whose **swap-square** content this theorem provides.
* L1224 (`def:boundary-exposure`) — the per-step boundary exposure
  whose two-step composition swap-commutes (modulo `BoundaryTwoStepSwap`).
-/

universe u

namespace TraceCalc
namespace LayerB
namespace RealObjects

namespace RewriteCalculusSetup

open CompletedReconstructionRecord

variable {setup : RewriteCalculusSetup.{u}}

/-! ### Equation lemmas for `peelSinkOtherIdx.val` -/

/-- `peelSinkOtherIdx.val` in the lower branch (`t.val < s.val`). -/
lemma peelSinkOtherIdx_val_lt {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : t ≠ s) (h : t.val < s.val) :
    (peelSinkOtherIdx s t hne).val = t.val := by
  unfold peelSinkOtherIdx
  rw [dif_pos h]

/-- `peelSinkOtherIdx.val` in the upper branch (`s.val < t.val`). -/
lemma peelSinkOtherIdx_val_ge {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : t ≠ s) (h : ¬ t.val < s.val) :
    (peelSinkOtherIdx s t hne).val = t.val - 1 := by
  unfold peelSinkOtherIdx
  rw [dif_neg h]

/-! ### Double-`embedSkip` commutation -/

/-- **Index commutation lemma.** For distinct `s, t : Fin R.n` and any
`i : Fin (R.n - 2)`, the two double-`embedSkip` maps agree as
`Fin R.n`-values:

```
embedSkip s (embedSkip (peelSinkOtherIdx s t _) i)
  = embedSkip t (embedSkip (peelSinkOtherIdx t s _) i)
```

Both sides skip the two original positions `s` and `t` in opposite
orders; the resulting `Fin R.n` index agrees pointwise on `.val` (one
of three integer outputs depending on `i.val`'s relation to
`min s.val t.val` and `max s.val t.val`). -/
theorem embedSkip_swap {R : CompletedReconstructionRecord setup}
    (s t : Fin R.n) (hne : s ≠ t) (i : Fin (R.n - 1 - 1)) :
    embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)
      = embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i) := by
  -- Reduce to a `.val`-level identity.
  apply Fin.ext
  -- We will produce the common value `v` and show both sides have val = v.
  -- Total ambient: s ≠ t means s.val ≠ t.val.
  have hval_ne : s.val ≠ t.val := fun h => hne (Fin.ext h)
  -- Abbreviations.
  set sv := s.val
  set tv := t.val
  set iv := i.val with hiv
  -- The two `peelSinkOtherIdx` values:
  -- `peelSinkOtherIdx s t _`.val = tv if tv < sv else tv - 1
  -- `peelSinkOtherIdx t s _`.val = sv if sv < tv else sv - 1
  -- Bounds on iv.
  have hi_bound : iv < R.n - 1 - 1 := i.isLt
  have hs_bound : sv < R.n := s.isLt
  have ht_bound : tv < R.n := t.isLt
  -- WLOG: split on sv < tv vs tv < sv.
  rcases Nat.lt_or_gt_of_ne hval_ne with hst | hts
  · -- Case sv < tv.
    -- pst.val = tv - 1 (since ¬ tv < sv).
    have hpst : (peelSinkOtherIdx s t (Ne.symm hne)).val = tv - 1 :=
      peelSinkOtherIdx_val_ge s t _ (by omega)
    -- pts.val = sv (since sv < tv).
    have hpts : (peelSinkOtherIdx t s hne).val = sv :=
      peelSinkOtherIdx_val_lt t s _ hst
    -- Inner embedSkip on LHS: `embedSkip pst i`. Splits on iv < tv - 1.
    -- Inner embedSkip on RHS: `embedSkip pts i`. Splits on iv < sv.
    by_cases hi_s : iv < sv
    · -- iv < sv < tv. Inner pst: iv < tv-1 (since sv ≤ tv-1), so val = iv.
      -- Outer s: iv < sv, val = iv.
      -- Inner pts: iv < sv, val = iv. Outer t: iv < sv < tv, val = iv.
      have hi_pst : iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
        rw [hpst]; omega
      have hi_pts : iv < (peelSinkOtherIdx t s hne).val := by
        rw [hpts]; exact hi_s
      have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv :=
        embedSkip_lt _ _ hi_pst
      have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv :=
        embedSkip_lt _ _ hi_pts
      have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv := by
        rw [embedSkip_lt _ _ (by rw [hL_inner]; exact hi_s)]
        exact hL_inner
      have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv := by
        rw [embedSkip_lt _ _ (by rw [hR_inner]; omega)]
        exact hR_inner
      rw [hL, hR]
    · -- iv ≥ sv. Need finer split: iv < tv - 1 vs iv ≥ tv - 1.
      by_cases hi_t : iv < tv - 1
      · -- sv ≤ iv < tv - 1. LHS inner pst: iv < tv-1, val = iv.
        -- Outer s: iv ≥ sv, val = iv + 1.
        -- RHS inner pts: iv ≥ sv (= pts.val), val = iv + 1.
        -- Outer t: iv + 1 vs tv. iv + 1 ≤ tv - 1 < tv, so val = iv + 1.
        have hi_pst : iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
          rw [hpst]; exact hi_t
        have hi_pts_not : ¬ iv < (peelSinkOtherIdx t s hne).val := by
          rw [hpts]; exact hi_s
        have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv :=
          embedSkip_lt _ _ hi_pst
        have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pts_not
        have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv + 1 := by
          rw [embedSkip_ge _ _ (by rw [hL_inner]; exact hi_s)]
          rw [hL_inner]
        have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv + 1 := by
          rw [embedSkip_lt _ _ (by rw [hR_inner]; omega)]
          exact hR_inner
        rw [hL, hR]
      · -- iv ≥ tv - 1. Combined with sv < tv this means iv ≥ tv - 1 ≥ sv.
        -- LHS inner pst: iv ≥ tv - 1 = pst.val, val = iv + 1.
        -- Outer s: iv + 1 vs sv. Since iv ≥ sv, iv + 1 > sv, val = iv + 2.
        -- RHS inner pts: iv ≥ sv = pts.val, val = iv + 1.
        -- Outer t: iv + 1 vs tv. iv ≥ tv - 1 → iv + 1 ≥ tv, val = iv + 2.
        have hi_pst_not : ¬ iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
          rw [hpst]; exact hi_t
        have hi_pts_not : ¬ iv < (peelSinkOtherIdx t s hne).val := by
          rw [hpts]; exact hi_s
        have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pst_not
        have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pts_not
        have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv + 2 := by
          rw [embedSkip_ge _ _ (by rw [hL_inner]; omega)]
          rw [hL_inner]
        have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv + 2 := by
          rw [embedSkip_ge _ _ (by rw [hR_inner]; omega)]
          rw [hR_inner]
        rw [hL, hR]
  · -- Case tv < sv. Symmetric to the above with roles of s and t swapped.
    have hpst : (peelSinkOtherIdx s t (Ne.symm hne)).val = tv :=
      peelSinkOtherIdx_val_lt s t _ hts
    have hpts : (peelSinkOtherIdx t s hne).val = sv - 1 :=
      peelSinkOtherIdx_val_ge t s _ (by omega)
    by_cases hi_t : iv < tv
    · -- iv < tv < sv.
      have hi_pst : iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
        rw [hpst]; exact hi_t
      have hi_pts : iv < (peelSinkOtherIdx t s hne).val := by
        rw [hpts]; omega
      have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv :=
        embedSkip_lt _ _ hi_pst
      have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv :=
        embedSkip_lt _ _ hi_pts
      have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv := by
        rw [embedSkip_lt _ _ (by rw [hL_inner]; omega)]
        exact hL_inner
      have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv := by
        rw [embedSkip_lt _ _ (by rw [hR_inner]; exact hi_t)]
        exact hR_inner
      rw [hL, hR]
    · by_cases hi_s : iv < sv - 1
      · -- tv ≤ iv < sv - 1.
        have hi_pst_not : ¬ iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
          rw [hpst]; exact hi_t
        have hi_pts : iv < (peelSinkOtherIdx t s hne).val := by
          rw [hpts]; exact hi_s
        have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pst_not
        have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv :=
          embedSkip_lt _ _ hi_pts
        have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv + 1 := by
          rw [embedSkip_lt _ _ (by rw [hL_inner]; omega)]
          exact hL_inner
        have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv + 1 := by
          rw [embedSkip_ge _ _ (by rw [hR_inner]; omega)]
          rw [hR_inner]
        rw [hL, hR]
      · -- iv ≥ sv - 1.
        have hi_pst_not : ¬ iv < (peelSinkOtherIdx s t (Ne.symm hne)).val := by
          rw [hpst]; exact hi_t
        have hi_pts_not : ¬ iv < (peelSinkOtherIdx t s hne).val := by
          rw [hpts]; exact hi_s
        have hL_inner : (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pst_not
        have hR_inner : (embedSkip (peelSinkOtherIdx t s hne) i).val = iv + 1 :=
          embedSkip_ge _ _ hi_pts_not
        have hL : (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm hne)) i)).val = iv + 2 := by
          rw [embedSkip_ge _ _ (by rw [hL_inner]; omega)]
          rw [hL_inner]
        have hR : (embedSkip t (embedSkip (peelSinkOtherIdx t s hne) i)).val = iv + 2 := by
          rw [embedSkip_ge _ _ (by rw [hR_inner]; omega)]
          rw [hR_inner]
        rw [hL, hR]

/-! ### Local generating relation `BoundaryTwoStepSwap` -/

/-- **The local generating relation for one independent-sink swap.**

`BoundaryTwoStepSwap h Y₁ Y₂` holds **exactly** when `Y₁` and `Y₂` are
the two literal `.Y` boundary objects produced by deleting the
independent sinks `s` and `t` in opposite orders. It has one
constructor and is intentionally **not** reflexive, symmetric, or
transitive — it is a *generator*, to be wrapped by `BoundaryAdminEquiv`
for global use.

Per user's verbatim 5e-ii directive: "keep `BoundaryTwoStepSwap` as a
local generating relation only. Do not force it to be reflexive or
transitive." -/
inductive BoundaryTwoStepSwap
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t) :
    setup.BoundaryObject → setup.BoundaryObject → Prop
  | swap :
      BoundaryTwoStepSwap h
        (peelSink (peelSink R s)
          (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))).Y
        (peelSink (peelSink R t)
          (peelSinkOtherIdx t s h.s_ne_t)).Y

/-! ### The swap-square theorem -/

/-- **`peelSink_swap_structEquiv`** (Phase 3B item 5e installment 2).

For two independent sinks `s, t` of `R`, the two two-step peelings
are `RecordStructEquiv` along `BR := BoundaryTwoStepSwap h`:

* **Interior** fields (`n`, `X`, `externalIn`, `packetIn`, `packetOut`,
  `packets`, `dep`, `attach`) match strictly via `embedSkip_swap`.
* **External output** lists differ by an adjacent block swap
  `(L ++ A) ++ B ~ (L ++ B) ++ A`, certified by `List.Perm`.
* **Boundary object** `Y` is related by the tautological
  `BoundaryTwoStepSwap.swap` constructor.

This is exactly the theorem shape demanded by the manuscript at
`thm:canonical-reconstruction-algorithm` (L1180): canonical
reconstruction is "all deletion orders are equivalent after accounting
for administrative boundary ordering." -/
theorem peelSink_swap_structEquiv
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t) :
    RecordStructEquiv (BoundaryTwoStepSwap h)
      (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
      (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t)) where
  n_eq := rfl
  X_eq := rfl
  Y_rel := BoundaryTwoStepSwap.swap
  externalIn_eq := rfl
  externalOut_perm := by
    show List.Perm
      ((R.ports.externalOut ++ R.ports.packetIn s) ++
        R.ports.packetIn (embedSkip s (peelSinkOtherIdx s t (Ne.symm h.s_ne_t))))
      ((R.ports.externalOut ++ R.ports.packetIn t) ++
        R.ports.packetIn (embedSkip t (peelSinkOtherIdx t s h.s_ne_t)))
    rw [embedSkip_peelSinkOtherIdx, embedSkip_peelSinkOtherIdx]
    rw [List.append_assoc, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  packetIn_eq := fun i => by
    show R.ports.packetIn
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) i))
      = R.ports.packetIn
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl i)))
    congr 1
    exact embedSkip_swap s t h.s_ne_t i
  packetOut_eq := fun i => by
    show R.ports.packetOut
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) i))
      = R.ports.packetOut
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl i)))
    congr 1
    exact embedSkip_swap s t h.s_ne_t i
  packets_eq := fun i => by
    show R.packets
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) i))
      = R.packets
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl i)))
    congr 1
    exact embedSkip_swap s t h.s_ne_t i
  dep_edge_eq := fun i j => by
    show R.dep.edge
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) i))
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) j))
      = R.dep.edge
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl i)))
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl j)))
    congr 1
    · exact embedSkip_swap s t h.s_ne_t i
    · exact embedSkip_swap s t h.s_ne_t j
  attach_eq := fun i => by
    show R.attach
        (embedSkip s (embedSkip (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)) i))
      = R.attach
        (embedSkip t (embedSkip (peelSinkOtherIdx t s h.s_ne_t) (Fin.cast rfl i)))
    congr 1
    exact embedSkip_swap s t h.s_ne_t i

/-! ### The administrative closure `BoundaryAdminEquiv` -/

/-- **The administrative closure of `BoundaryTwoStepSwap`.**

The free equivalence relation generated by all `BoundaryTwoStepSwap`
instances. This is the `BR` to plug into `RecordStructEquiv` for
**global** administrative chain equivalence (downstream items 5f and
the canonicality clause of `thm:canonical-reconstruction-algorithm`).

Per user's verbatim 5e-ii directive: "After [`peelSink_swap_structEquiv`],
introduce `BoundaryAdminEquiv` as the closure used for global
administrative chain equivalence." -/
inductive BoundaryAdminEquiv :
    setup.BoundaryObject → setup.BoundaryObject → Prop
  | refl (Y : setup.BoundaryObject) : BoundaryAdminEquiv Y Y
  | symm {Y₁ Y₂ : setup.BoundaryObject} :
      BoundaryAdminEquiv Y₁ Y₂ → BoundaryAdminEquiv Y₂ Y₁
  | trans {Y₁ Y₂ Y₃ : setup.BoundaryObject} :
      BoundaryAdminEquiv Y₁ Y₂ → BoundaryAdminEquiv Y₂ Y₃ →
        BoundaryAdminEquiv Y₁ Y₃
  | ofTwoStepSwap {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
      {h : IndependentSinks R s t} {Y₁ Y₂ : setup.BoundaryObject} :
      BoundaryTwoStepSwap h Y₁ Y₂ → BoundaryAdminEquiv Y₁ Y₂

namespace BoundaryAdminEquiv

/-- Reflexivity, packaged as a function suitable for
`RecordStructEquiv.refl`. -/
theorem refl' (Y : setup.BoundaryObject) :
    @BoundaryAdminEquiv setup Y Y := BoundaryAdminEquiv.refl Y

/-- Symmetry, packaged for `RecordStructEquiv.symm`. -/
theorem symm' {Y₁ Y₂ : setup.BoundaryObject} (h : BoundaryAdminEquiv Y₁ Y₂) :
    BoundaryAdminEquiv Y₂ Y₁ := h.symm

/-- Transitivity, packaged for `RecordStructEquiv.trans`. -/
theorem trans' {Y₁ Y₂ Y₃ : setup.BoundaryObject}
    (h₁ : BoundaryAdminEquiv Y₁ Y₂) (h₂ : BoundaryAdminEquiv Y₂ Y₃) :
    BoundaryAdminEquiv Y₁ Y₃ := h₁.trans h₂

end BoundaryAdminEquiv

/-- Lift the local swap-square theorem along the closure embedding.
This is the form `RecordStructEquiv BoundaryAdminEquiv ...` consumers
will use downstream once `BoundaryAdminEquiv` becomes the chosen
global `BR`. -/
theorem peelSink_swap_structEquiv_admin
    {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t) :
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
      (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t)) :=
  let h₀ := peelSink_swap_structEquiv h
  { n_eq := h₀.n_eq
    X_eq := h₀.X_eq
    Y_rel := BoundaryAdminEquiv.ofTwoStepSwap h₀.Y_rel
    externalIn_eq := h₀.externalIn_eq
    externalOut_perm := h₀.externalOut_perm
    packetIn_eq := h₀.packetIn_eq
    packetOut_eq := h₀.packetOut_eq
    packets_eq := h₀.packets_eq
    dep_edge_eq := h₀.dep_edge_eq
    attach_eq := h₀.attach_eq }

/-
TEX ref: our_paper_draft.tex, label thm:tensor-factor-independence (L1168+)
Paper role: the reconstruction of a tensor-decomposed record is independent of
  the order in which the tensor factors are processed; proved via swap-square
  commutativity of independent sinks
Lean status: MISSING → stub added (M2)
-/
/-- **`thm:tensor-factor-independence`**: the canonical reconstruction of a
record with multiple tensor factors is independent of the order in which
those factors' sinks are peeled.

Concretely: peeling independent sinks `s` and `t` in either order yields
admin-equivalent results. This follows from `peelSink_swap_structEquiv_admin`:
the two-step peel `s → t` and `t → s` produce structurally equivalent records.

The full tensor-factor independence theorem additionally requires that the
WCC decomposition aligns with the independence of sink choices (C3 of
`IsCompleted`), which is recorded here as a Prop-valued obligation. -/
structure TensorFactorIndependence
    (setup : RewriteCalculusSetup.{u}) where
  /-- The swap square holds: peeling `s` then `t` gives the same result
  (up to admin equivalence) as peeling `t` then `s`, for any two
  independent sinks. -/
  swap_square :
    ∀ {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
      (h : IndependentSinks R s t),
      RecordStructEquiv (@BoundaryAdminEquiv setup)
        (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
        (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t))
  /-- The full independence: the reconstruction of a tensor product factors
  canonically through the component reconstructions. -/
  tensor_reconstruction_independence : Prop

/-- The swap-square half of tensor-factor independence holds from
`peelSink_swap_structEquiv_admin`. -/
def tensorFactorIndependence_swap_square_holds
    (setup : RewriteCalculusSetup.{u}) : Prop :=
  ∀ {R : CompletedReconstructionRecord setup} {s t : Fin R.n}
    (h : IndependentSinks R s t),
    RecordStructEquiv (@BoundaryAdminEquiv setup)
      (peelSink (peelSink R s) (peelSinkOtherIdx s t (Ne.symm h.s_ne_t)))
      (peelSink (peelSink R t) (peelSinkOtherIdx t s h.s_ne_t))

theorem tensorFactorIndependence_swap_square_holds_proof
    (setup : RewriteCalculusSetup.{u}) :
    tensorFactorIndependence_swap_square_holds setup :=
  fun h => peelSink_swap_structEquiv_admin h

end RewriteCalculusSetup

end RealObjects
end LayerB
end TraceCalc
