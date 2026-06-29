import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPacketLabels.ZetaCenteredNormalization.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaPolynomialTailSummability.Owner
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Boundary prime-power windows

This file owns the finite prime-power windows used by the completed-square
form of the zeta explicit formula.  The old packet labels can still be used as
a display layer, but the analytic owner object is a prime-power index with its
prime and exponent conditions visible.
-/

namespace Boundary
namespace LFunctions

noncomputable section
open scoped BigOperators

/-- A prime-power coordinate before imposing primality and positive exponent conditions. -/
structure ZetaPrimePowerIndex where
  p : ℕ
  n : ℕ
deriving DecidableEq

namespace ZetaPrimePowerIndex

/-- The predicate saying that a coordinate is a genuine prime power. -/
def IsGenuine (ι : ZetaPrimePowerIndex) : Prop :=
  Nat.Prime ι.p ∧ 1 ≤ ι.n

/-- The logarithmic center of a prime-power coordinate. -/
def center (ι : ZetaPrimePowerIndex) : ℝ :=
  zetaPrimePacketCenter ι.p ι.n

/-- Rectangular height of a raw prime-power coordinate. -/
def height (ι : ZetaPrimePowerIndex) : ℕ :=
  max ι.p ι.n

/-- Polynomial decay in the rectangular prime-power height. -/
noncomputable def polynomialHeightDecay
    (k : ℕ) (ι : ZetaPrimePowerIndex) : ℝ :=
  (1 + ‖((ι.height : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))

/-- The total shell mass allowed at rectangular height `m`.

The shell of indices with `max p n = m` has linear cardinality in `m`; this one-dimensional
majorant is the honest counting object behind rectangular height summability. -/
noncomputable def polynomialHeightShellMass
    (k m : ℕ) : ℝ :=
  ((2 * (m + 1) : ℕ) : ℝ) *
    (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))

/-- The unfiltered rectangular box of raw prime-power coordinates. -/
def rawBox (N : ℕ) : Finset ZetaPrimePowerIndex :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).map
    ⟨fun q => ⟨q.1, q.2⟩, by
      intro q r hqr
      cases q
      cases r
      cases hqr
      rfl⟩

/-- Membership in the raw rectangular box is coordinatewise boundedness. -/
theorem mem_rawBox_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ rawBox N ↔ ι.p < N + 1 ∧ ι.n < N + 1 := by
  constructor
  · intro hι
    unfold rawBox at hι
    rcases Finset.mem_map.mp hι with ⟨q, hq, hqι⟩
    rcases q with ⟨p, n⟩
    have hp : p < N + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hq).1
    have hn : n < N + 1 :=
      Finset.mem_range.mp (Finset.mem_product.mp hq).2
    cases hqι
    exact ⟨hp, hn⟩
  · intro hι
    unfold rawBox
    refine Finset.mem_map.mpr ?_
    refine ⟨(ι.p, ι.n), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hι.1, Finset.mem_range.mpr hι.2⟩

/-- The finite rectangular shell of raw prime-power coordinates at exact height `m`. -/
def heightShell (m : ℕ) : Finset ZetaPrimePowerIndex :=
  (rawBox m).filter (fun ι => ι.height = m)

/-- The vertical edge of the rectangular shell, where the prime coordinate realizes the
height. -/
def heightShellVerticalEdge (m : ℕ) : Finset ZetaPrimePowerIndex :=
  (rawBox m).filter (fun ι => ι.p = m)

/-- The horizontal edge of the rectangular shell, where the exponent coordinate realizes the
height. -/
def heightShellHorizontalEdge (m : ℕ) : Finset ZetaPrimePowerIndex :=
  (rawBox m).filter (fun ι => ι.n = m)

/-- The explicit range model for the vertical rectangular edge at height `m`. -/
def heightShellVerticalEdgeModel (m : ℕ) : Finset ZetaPrimePowerIndex :=
  (Finset.range (m + 1)).map
    ⟨fun n => ⟨m, n⟩, by
      intro n₁ n₂ hn
      cases hn
      rfl⟩

/-- The explicit range model for the horizontal rectangular edge at height `m`. -/
def heightShellHorizontalEdgeModel (m : ℕ) : Finset ZetaPrimePowerIndex :=
  (Finset.range (m + 1)).map
    ⟨fun p => ⟨p, m⟩, by
      intro p₁ p₂ hp
      cases hp
      rfl⟩

/-- Membership in an exact rectangular height shell is exactly equality of rectangular
height with the shell parameter. -/
theorem mem_heightShell_iff
    (m : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ heightShell m ↔ ι.height = m := by
  constructor
  · intro hι
    unfold heightShell at hι
    exact (Finset.mem_filter.mp hι).2
  · intro hheight
    unfold heightShell
    refine Finset.mem_filter.mpr ?_
    have hp_le : ι.p ≤ m :=
      le_trans (Nat.le_max_left ι.p ι.n) (le_of_eq hheight)
    have hn_le : ι.n ≤ m :=
      le_trans (Nat.le_max_right ι.p ι.n) (le_of_eq hheight)
    have hraw : ι ∈ rawBox m :=
      (mem_rawBox_iff m ι).mpr
        ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩
    exact ⟨hraw, hheight⟩

/-- Rectangular-height decay is constant on an exact height shell. -/
theorem polynomialHeightDecay_eq_on_heightShell
    (k m : ℕ) (ι : ZetaPrimePowerIndex)
    (hι : ι ∈ heightShell m) :
    polynomialHeightDecay k ι =
      (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) := by
  have hheight : ι.height = m :=
    (mem_heightShell_iff m ι).mp hι
  unfold polynomialHeightDecay
  exact congrArg
    (fun h : ℕ => (1 + ‖((h : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)))
    hheight

/-- Every exact rectangular height-shell point lies on one of the two boundary edges. -/
theorem heightShell_mem_vertical_or_horizontal
    (m : ℕ) (ι : ZetaPrimePowerIndex)
    (hι : ι ∈ heightShell m) :
    ι ∈ heightShellVerticalEdge m ∨
      ι ∈ heightShellHorizontalEdge m := by
  have hraw : ι ∈ rawBox m := (Finset.mem_filter.mp hι).1
  have hheight : ι.height = m := (Finset.mem_filter.mp hι).2
  by_cases hp_eq : ι.p = m
  · left
    unfold heightShellVerticalEdge
    exact Finset.mem_filter.mpr ⟨hraw, hp_eq⟩
  · right
    have hp_le : ι.p ≤ m :=
      le_trans (Nat.le_max_left ι.p ι.n) (le_of_eq hheight)
    have hn_le : ι.n ≤ m :=
      le_trans (Nat.le_max_right ι.p ι.n) (le_of_eq hheight)
    have hp_lt : ι.p < m :=
      Nat.lt_of_le_of_ne hp_le hp_eq
    have hn_eq : ι.n = m := by
      exact Nat.le_antisymm hn_le
        (le_of_not_gt
          (fun hn_lt =>
          have hmax_lt : max ι.p ι.n < m :=
            max_lt hp_lt hn_lt
          have hm_le_max : m ≤ max ι.p ι.n :=
            le_of_eq hheight.symm
          (not_lt_of_ge hm_le_max) hmax_lt))
    unfold heightShellHorizontalEdge
    exact Finset.mem_filter.mpr ⟨hraw, hn_eq⟩

/-- The exact rectangular height shell is contained in the union of its two edges. -/
theorem heightShell_subset_edgeUnion
    (m : ℕ) :
    heightShell m ⊆
      heightShellVerticalEdge m ∪ heightShellHorizontalEdge m := by
  intro ι hι
  exact Finset.mem_union.mpr (heightShell_mem_vertical_or_horizontal m ι hι)

/-- The vertical filtered edge is the explicit finite range model. -/
theorem heightShellVerticalEdge_eq_model
    (m : ℕ) :
    heightShellVerticalEdge m = heightShellVerticalEdgeModel m := by
  apply Finset.ext
  intro ι
  constructor
  · intro hι
    have hraw : ι ∈ rawBox m := (Finset.mem_filter.mp hι).1
    have hp : ι.p = m := (Finset.mem_filter.mp hι).2
    have hn_lt : ι.n < m + 1 :=
      ((mem_rawBox_iff m ι).mp hraw).2
    unfold heightShellVerticalEdgeModel
    refine Finset.mem_map.mpr ?_
    refine ⟨ι.n, Finset.mem_range.mpr hn_lt, ?_⟩
    cases hp
    rfl
  · intro hι
    unfold heightShellVerticalEdgeModel at hι
    rcases Finset.mem_map.mp hι with ⟨n, hn_range, hn_eq⟩
    cases hn_eq
    unfold heightShellVerticalEdge
    refine Finset.mem_filter.mpr ?_
    have hraw : ({ p := m, n := n } : ZetaPrimePowerIndex) ∈ rawBox m :=
      (mem_rawBox_iff m ({ p := m, n := n } : ZetaPrimePowerIndex)).mpr
        ⟨Nat.lt_succ_self m, Finset.mem_range.mp hn_range⟩
    exact ⟨hraw, rfl⟩

/-- The horizontal filtered edge is the explicit finite range model. -/
theorem heightShellHorizontalEdge_eq_model
    (m : ℕ) :
    heightShellHorizontalEdge m = heightShellHorizontalEdgeModel m := by
  apply Finset.ext
  intro ι
  constructor
  · intro hι
    have hraw : ι ∈ rawBox m := (Finset.mem_filter.mp hι).1
    have hn : ι.n = m := (Finset.mem_filter.mp hι).2
    have hp_lt : ι.p < m + 1 :=
      ((mem_rawBox_iff m ι).mp hraw).1
    unfold heightShellHorizontalEdgeModel
    refine Finset.mem_map.mpr ?_
    refine ⟨ι.p, Finset.mem_range.mpr hp_lt, ?_⟩
    cases hn
    rfl
  · intro hι
    unfold heightShellHorizontalEdgeModel at hι
    rcases Finset.mem_map.mp hι with ⟨p, hp_range, hp_eq⟩
    cases hp_eq
    unfold heightShellHorizontalEdge
    refine Finset.mem_filter.mpr ?_
    have hraw : ({ p := p, n := m } : ZetaPrimePowerIndex) ∈ rawBox m :=
      (mem_rawBox_iff m ({ p := p, n := m } : ZetaPrimePowerIndex)).mpr
        ⟨Finset.mem_range.mp hp_range, Nat.lt_succ_self m⟩
    exact ⟨hraw, rfl⟩

/-- The vertical edge model has exactly `m + 1` points. -/
theorem card_heightShellVerticalEdgeModel
    (m : ℕ) :
    (heightShellVerticalEdgeModel m).card = m + 1 := by
  unfold heightShellVerticalEdgeModel
  exact Eq.trans
    (Finset.card_map
      (⟨fun n => ⟨m, n⟩, by
        intro n₁ n₂ hn
        cases hn
        rfl⟩ : ℕ ↪ ZetaPrimePowerIndex))
    (Finset.card_range (m + 1))

/-- The horizontal edge model has exactly `m + 1` points. -/
theorem card_heightShellHorizontalEdgeModel
    (m : ℕ) :
    (heightShellHorizontalEdgeModel m).card = m + 1 := by
  unfold heightShellHorizontalEdgeModel
  exact Eq.trans
    (Finset.card_map
      (⟨fun p => ⟨p, m⟩, by
        intro p₁ p₂ hp
        cases hp
        rfl⟩ : ℕ ↪ ZetaPrimePowerIndex))
    (Finset.card_range (m + 1))

/-- The exact height shell is covered by its two rectangular edges. -/
theorem card_heightShell_le_edgeCard_sum
    (m : ℕ) :
    (heightShell m).card ≤
      (heightShellVerticalEdge m).card + (heightShellHorizontalEdge m).card := by
  have hsubset :
      (heightShell m).card ≤
        (heightShellVerticalEdge m ∪ heightShellHorizontalEdge m).card :=
    Finset.card_le_card (heightShell_subset_edgeUnion m)
  have hunion :
      (heightShellVerticalEdge m ∪ heightShellHorizontalEdge m).card ≤
        (heightShellVerticalEdge m).card + (heightShellHorizontalEdge m).card :=
    Finset.card_union_le (heightShellVerticalEdge m) (heightShellHorizontalEdge m)
  exact le_trans hsubset hunion

/-- The vertical edge of an exact height shell has at most `m + 1` points. -/
theorem card_heightShellVerticalEdge_le
    (m : ℕ) :
    (heightShellVerticalEdge m).card ≤ m + 1 := by
  have hedge :
      (heightShellVerticalEdge m).card =
        (heightShellVerticalEdgeModel m).card :=
    congrArg Finset.card (heightShellVerticalEdge_eq_model m)
  exact Eq.subst
    (motive := fun c : ℕ => c ≤ m + 1)
    hedge.symm
    (le_of_eq (card_heightShellVerticalEdgeModel m))

/-- The horizontal edge of an exact height shell has at most `m + 1` points. -/
theorem card_heightShellHorizontalEdge_le
    (m : ℕ) :
    (heightShellHorizontalEdge m).card ≤ m + 1 := by
  have hedge :
      (heightShellHorizontalEdge m).card =
        (heightShellHorizontalEdgeModel m).card :=
    congrArg Finset.card (heightShellHorizontalEdge_eq_model m)
  exact Eq.subst
    (motive := fun c : ℕ => c ≤ m + 1)
    hedge.symm
    (le_of_eq (card_heightShellHorizontalEdgeModel m))

/-- Twice a successor is the sum of two copies of that successor. -/
theorem add_succ_self_eq_two_mul_succ
    (m : ℕ) :
    (m + 1) + (m + 1) = 2 * (m + 1) := by
  exact (Nat.two_mul (m + 1)).symm

/-- Exact rectangular height shells have at most linear cardinality. -/
theorem card_heightShell_le_linear
    (m : ℕ) :
    (heightShell m).card ≤ 2 * (m + 1) := by
  have hcover :
      (heightShell m).card ≤
        (heightShellVerticalEdge m).card + (heightShellHorizontalEdge m).card :=
    card_heightShell_le_edgeCard_sum m
  have hvertical :
      (heightShellVerticalEdge m).card ≤ m + 1 :=
    card_heightShellVerticalEdge_le m
  have hhorizontal :
      (heightShellHorizontalEdge m).card ≤ m + 1 :=
    card_heightShellHorizontalEdge_le m
  have hedge :
      (heightShellVerticalEdge m).card + (heightShellHorizontalEdge m).card ≤
        (m + 1) + (m + 1) :=
    add_le_add hvertical hhorizontal
  exact le_trans hcover
    (le_trans hedge (le_of_eq (add_succ_self_eq_two_mul_succ m)))

/-- The linear shell cardinality bound transported to real scalars. -/
theorem card_heightShell_le_linear_real
    (m : ℕ) :
    ((heightShell m).card : ℝ) ≤ ((2 * (m + 1) : ℕ) : ℝ) := by
  exact Nat.cast_le.mpr (card_heightShell_le_linear m)

/-- Summing a real constant over a finite set gives cardinality times that constant. -/
theorem finset_sum_const_real
    {α : Type} (s : Finset α) (c : ℝ) :
    (∑ _x in s, c) = (s.card : ℝ) * c := by
  calc
    (∑ _x in s, c) = s.card • c := by
      exact Finset.sum_const c
    _ = (s.card : ℝ) * c := by
      exact nsmul_eq_mul s.card c

/-- The finite shell sum of rectangular-height decay at exact height `m`. -/
noncomputable def polynomialHeightShellSum
    (k m : ℕ) : ℝ :=
  ∑ ι in heightShell m, polynomialHeightDecay k ι

/-- The exact-height shell sum is the sum of a constant over that shell. -/
theorem polynomialHeightShellSum_eq_sum_const_decay
    (k m : ℕ) :
    polynomialHeightShellSum k m =
      ∑ _ι in heightShell m,
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) := by
  unfold polynomialHeightShellSum
  exact Finset.sum_congr rfl
    (fun ι hι => polynomialHeightDecay_eq_on_heightShell k m ι hι)

/-- The exact-height shell sum is the shell cardinality times the shell decay. -/
theorem polynomialHeightShellSum_eq_card_mul_decay
    (k m : ℕ) :
    polynomialHeightShellSum k m =
      ((heightShell m).card : ℝ) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) := by
  have hsum :
      polynomialHeightShellSum k m =
        ∑ _ι in heightShell m,
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    polynomialHeightShellSum_eq_sum_const_decay k m
  have hconst :
      (∑ _ι in heightShell m,
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))) =
        ((heightShell m).card : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    finset_sum_const_real
      (heightShell m)
      ((1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)))
  exact Eq.trans hsum hconst

/-- The exact-height shell sum is bounded by the declared shell mass. -/
theorem polynomialHeightShellSum_le_shellMass
    (k m : ℕ) :
    polynomialHeightShellSum k m ≤ polynomialHeightShellMass k m := by
  have hsum :
      polynomialHeightShellSum k m =
        ((heightShell m).card : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    polynomialHeightShellSum_eq_card_mul_decay k m
  have hcard :
      ((heightShell m).card : ℝ) ≤ ((2 * (m + 1) : ℕ) : ℝ) := by
    exact card_heightShell_le_linear_real m
  have hdecay_nonneg :
      0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) := by
    exact zpow_nonneg
      (add_nonneg zero_le_one (norm_nonneg ((m : ℕ) : ℝ)))
      (-(k + 3 : ℤ))
  have hmul :
      ((heightShell m).card : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) ≤
        ((2 * (m + 1) : ℕ) : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    mul_le_mul_of_nonneg_right hcard hdecay_nonneg
  unfold polynomialHeightShellMass
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ((2 * (m + 1) : ℕ) : ℝ) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)))
    hsum.symm
    hmul

/-- Exact-height shell sums are nonnegative. -/
theorem polynomialHeightShellSum_nonnegative
    (k m : ℕ) :
    0 ≤ polynomialHeightShellSum k m := by
  have hsum :
      polynomialHeightShellSum k m =
        ((heightShell m).card : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    polynomialHeightShellSum_eq_card_mul_decay k m
  have hcard_nonneg :
      0 ≤ ((heightShell m).card : ℝ) :=
    Nat.cast_nonneg (heightShell m).card
  have hdecay_nonneg :
      0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one (norm_nonneg ((m : ℕ) : ℝ)))
      (-(k + 3 : ℤ))
  exact Eq.subst
    (motive := fun v : ℝ => 0 ≤ v)
    hsum.symm
    (mul_nonneg hcard_nonneg hdecay_nonneg)

/-- A nonnegative real sequence dominated by a summable real sequence is summable. -/
theorem summable_of_nonnegative_le_summable_real
    (a b : ℕ → ℝ)
    (ha_nonneg : ∀ n : ℕ, 0 ≤ a n)
    (hab : ∀ n : ℕ, a n ≤ b n)
    (hb : Summable b) :
    Summable a := by
  exact Summable.of_norm_bounded b hb
    (fun n => by
      have ha_norm : ‖a n‖ = a n :=
        Real.norm_of_nonneg (ha_nonneg n)
      exact Eq.subst
        (motive := fun lhs : ℝ => lhs ≤ b n)
        ha_norm.symm
        (hab n))

/-- The linear cardinal majorant is bounded by twice the height base. -/
theorem linear_shell_card_factor_le_two_mul_heightBase
    (m : ℕ) :
    ((2 * (m + 1) : ℕ) : ℝ) ≤
      2 * (1 + ‖((m : ℕ) : ℝ)‖) := by
  have hm_nonneg : 0 ≤ ((m : ℕ) : ℝ) :=
    Nat.cast_nonneg m
  have hnorm : ‖((m : ℕ) : ℝ)‖ = ((m : ℕ) : ℝ) :=
    Real.norm_of_nonneg hm_nonneg
  have hcast_mul :
      ((2 * (m + 1) : ℕ) : ℝ) =
        (2 : ℝ) * ((m + 1 : ℕ) : ℝ) := by
    exact Nat.cast_mul 2 (m + 1)
  have hcast_add :
      ((m + 1 : ℕ) : ℝ) = ((m : ℕ) : ℝ) + 1 := by
    exact Eq.trans
      (Nat.cast_add m 1)
      (congrArg (fun x : ℝ => ((m : ℕ) : ℝ) + x) Nat.cast_one)
  have htarget_eq :
      ((2 * (m + 1) : ℕ) : ℝ) =
        2 * (1 + ‖((m : ℕ) : ℝ)‖) := by
    calc
      ((2 * (m + 1) : ℕ) : ℝ) =
          (2 : ℝ) * ((m + 1 : ℕ) : ℝ) := hcast_mul
      _ = 2 * (((m : ℕ) : ℝ) + 1) := by
        exact congrArg (fun x : ℝ => (2 : ℝ) * x) hcast_add
      _ = 2 * (1 + ((m : ℕ) : ℝ)) := by
        exact congrArg (fun x : ℝ => (2 : ℝ) * x)
          (add_comm ((m : ℕ) : ℝ) 1)
      _ = 2 * (1 + ‖((m : ℕ) : ℝ)‖) := by
        exact congrArg (fun x : ℝ => (2 : ℝ) * (1 + x)) hnorm.symm
  exact le_of_eq htarget_eq

/-- One height-base factor cancels one negative-power step. -/
theorem heightBase_mul_negative_zpow_succ_le_negative_zpow
    (k m : ℕ) :
    (1 + ‖((m : ℕ) : ℝ)‖) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) ≤
      (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  let X : ℝ := 1 + ‖((m : ℕ) : ℝ)‖
  have hX_pos : 0 < X := by
    exact lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg ((m : ℕ) : ℝ)))
  have hX_ne : X ≠ 0 :=
    ne_of_gt hX_pos
  have hint :
      (1 : ℤ) + (-(k + 3 : ℤ)) = -(k + 2 : ℤ) := by
    have hsucc :
        (k + 3 : ℤ) = (k + 2 : ℤ) + 1 := by
      exact_mod_cast (Nat.add_assoc k 2 1).symm
    calc
      (1 : ℤ) + (-(k + 3 : ℤ)) =
          1 + -((k + 2 : ℤ) + 1) := by
        exact congrArg (fun x : ℤ => 1 + -x) hsucc
      _ = 1 + (-(k + 2 : ℤ) + -1) := by
        exact congrArg (fun x : ℤ => 1 + x)
          (neg_add (k + 2 : ℤ) 1)
      _ = 1 + (-1 + -(k + 2 : ℤ)) := by
        exact congrArg (fun x : ℤ => 1 + x)
          (add_comm (-(k + 2 : ℤ)) (-1))
      _ = (1 + -1) + -(k + 2 : ℤ) :=
        (add_assoc 1 (-1) (-(k + 2 : ℤ))).symm
      _ = 0 + -(k + 2 : ℤ) := by
        exact congrArg (fun x : ℤ => x + -(k + 2 : ℤ))
          (add_neg_cancel 1)
      _ = -(k + 2 : ℤ) := zero_add (-(k + 2 : ℤ))
  have hcombine :
      X * X ^ (-(k + 3 : ℤ)) =
        X ^ ((1 : ℤ) + (-(k + 3 : ℤ))) := by
    calc
      X * X ^ (-(k + 3 : ℤ)) =
          X ^ (1 : ℤ) * X ^ (-(k + 3 : ℤ)) := by
        exact congrArg
          (fun v : ℝ => v * X ^ (-(k + 3 : ℤ)))
          (zpow_one X).symm
      _ = X ^ ((1 : ℤ) + (-(k + 3 : ℤ))) := by
        exact (zpow_add₀ hX_ne (1 : ℤ) (-(k + 3 : ℤ))).symm
  have heq :
      X * X ^ (-(k + 3 : ℤ)) =
        X ^ (-(k + 2 : ℤ)) := by
    exact hcombine.trans (congrArg (fun n : ℤ => X ^ n) hint)
  exact le_of_eq heq

/-- The linear shell mass is pointwise dominated by a constant multiple of the
one-dimensional polynomial tail with one fewer decay power. -/
theorem linear_polynomialShellMassSequence_le_two_mul_tail
    (k m : ℕ) :
    ((2 * (m + 1) : ℕ) : ℝ) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) ≤
      2 * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) := by
  have hfactor :
      ((2 * (m + 1) : ℕ) : ℝ) ≤
        2 * (1 + ‖((m : ℕ) : ℝ)‖) :=
    linear_shell_card_factor_le_two_mul_heightBase m
  have hdecay_nonneg :
      0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    zpow_nonneg
      (add_nonneg zero_le_one (norm_nonneg ((m : ℕ) : ℝ)))
      (-(k + 3 : ℤ))
  have hstep :
      ((2 * (m + 1) : ℕ) : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) ≤
        (2 * (1 + ‖((m : ℕ) : ℝ)‖)) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
    mul_le_mul_of_nonneg_right hfactor hdecay_nonneg
  have hcancel :
      (1 + ‖((m : ℕ) : ℝ)‖) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) ≤
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
    heightBase_mul_negative_zpow_succ_le_negative_zpow k m
  have hscale :
      2 *
          ((1 + ‖((m : ℕ) : ℝ)‖) *
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))) ≤
        2 * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)) :=
    mul_le_mul_of_nonneg_left hcancel zero_le_two
  have hreassoc :
      (2 * (1 + ‖((m : ℕ) : ℝ)‖)) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) =
        2 *
          ((1 + ‖((m : ℕ) : ℝ)‖) *
            (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))) :=
    mul_assoc 2
      (1 + ‖((m : ℕ) : ℝ)‖)
      ((1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)))
  exact le_trans hstep
    (Eq.subst
      (motive := fun x : ℝ =>
        x ≤ 2 * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
      hreassoc.symm
      hscale)

/-- The constant multiple of the one-dimensional polynomial tail is summable. -/
theorem summable_two_mul_one_add_nat_norm_negative_zpow_succ
    (k : ℕ) :
    Summable
      (fun m : ℕ =>
        2 * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ))) := by
  exact (summable_one_add_nat_norm_negative_zpow_succ k).mul_left 2

/-- The one-dimensional polynomial shell mass sequence is summable. -/
theorem summable_linear_polynomialShellMassSequence
    (k : ℕ) :
    Summable
      (fun m : ℕ =>
        ((2 * (m + 1) : ℕ) : ℝ) *
          (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ))) := by
  exact summable_of_nonnegative_le_summable_real
    (fun m : ℕ =>
      ((2 * (m + 1) : ℕ) : ℝ) *
        (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)))
    (fun m : ℕ =>
      2 * (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 2 : ℤ)))
    (fun m : ℕ => by
      have hleft_nonneg : 0 ≤ ((2 * (m + 1) : ℕ) : ℝ) :=
        Nat.cast_nonneg (2 * (m + 1))
      have hright_nonneg :
          0 ≤ (1 + ‖((m : ℕ) : ℝ)‖) ^ (-(k + 3 : ℤ)) :=
        zpow_nonneg
          (add_nonneg zero_le_one (norm_nonneg ((m : ℕ) : ℝ)))
          (-(k + 3 : ℤ))
      exact mul_nonneg hleft_nonneg hright_nonneg)
    (fun m : ℕ => linear_polynomialShellMassSequence_le_two_mul_tail k m)
    (summable_two_mul_one_add_nat_norm_negative_zpow_succ k)

/-- Polynomial shell masses are summable over rectangular heights. -/
theorem summable_polynomialHeightShellMass
    (k : ℕ) :
    Summable (fun m : ℕ => polynomialHeightShellMass k m) := by
  exact summable_linear_polynomialShellMassSequence k

/-- Shell sums are summable when dominated by summable shell masses. -/
theorem summable_polynomialHeightShellSum_of_shellMass
    (k : ℕ)
    (hshell : Summable (fun m : ℕ => polynomialHeightShellMass k m)) :
    Summable (fun m : ℕ => polynomialHeightShellSum k m) := by
  exact summable_of_nonnegative_le_summable_real
    (fun m : ℕ => polynomialHeightShellSum k m)
    (fun m : ℕ => polynomialHeightShellMass k m)
    (fun m : ℕ => polynomialHeightShellSum_nonnegative k m)
    (fun m : ℕ => polynomialHeightShellSum_le_shellMass k m)
    hshell

/-- The finite fiber of raw indices at a fixed rectangular height. -/
def heightFiber (m : ℕ) : Type :=
  {ι : ZetaPrimePowerIndex // ι ∈ heightShell m}

instance heightFiber.fintype (m : ℕ) : Fintype (heightFiber m) :=
  Finset.Subtype.fintype (heightShell m)

/-- Rectangular-height decay is pointwise nonnegative. -/
theorem polynomialHeightDecay_nonnegative
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 ≤ polynomialHeightDecay k ι := by
  unfold polynomialHeightDecay
  exact zpow_nonneg
    (add_nonneg zero_le_one (norm_nonneg ((ι.height : ℕ) : ℝ)))
    (-(k + 3 : ℤ))

/-- Rectangular-height decay is pointwise strictly positive. -/
theorem polynomialHeightDecay_pos
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    0 < polynomialHeightDecay k ι := by
  unfold polynomialHeightDecay
  exact zpow_pos
    (one_add_nat_norm_pos ι.height)
    (-(k + 3 : ℤ))

/-- Rectangular-height decay is bounded by one. -/
theorem polynomialHeightDecay_le_one
    (k : ℕ) (ι : ZetaPrimePowerIndex) :
    polynomialHeightDecay k ι ≤ 1 := by
  let X : ℝ := 1 + ‖((ι.height : ℕ) : ℝ)‖
  have hX_one : 1 ≤ X := by
    exact le_add_of_nonneg_right (norm_nonneg ((ι.height : ℕ) : ℝ))
  have hexp : (-(k + 3 : ℤ)) ≤ 0 := by
    exact neg_nonpos.mpr (Int.ofNat_nonneg (k + 3))
  unfold polynomialHeightDecay
  change X ^ (-(k + 3 : ℤ)) ≤ 1
  calc
    X ^ (-(k + 3 : ℤ)) ≤ X ^ (0 : ℤ) := by
      exact zpow_le_zpow_right₀ hX_one hexp
    _ = 1 := by
      exact zpow_zero X

/-- Increasing the requested polynomial decay exponent only decreases the
rectangular-height decay majorant. -/
theorem polynomialHeightDecay_le_of_le
    {k l : ℕ} (hlk : l ≤ k) (ι : ZetaPrimePowerIndex) :
    polynomialHeightDecay k ι ≤ polynomialHeightDecay l ι := by
  let X : ℝ := 1 + ‖((ι.height : ℕ) : ℝ)‖
  have hX_one : 1 ≤ X := by
    exact le_add_of_nonneg_right (norm_nonneg ((ι.height : ℕ) : ℝ))
  have hexp : (-(k + 3 : ℤ)) ≤ -(l + 3 : ℤ) := by
    have hnat : l + 3 ≤ k + 3 :=
      Nat.add_le_add_right hlk 3
    have hint : (l + 3 : ℤ) ≤ (k + 3 : ℤ) :=
      Int.ofNat_le.mpr hnat
    exact neg_le_neg hint
  unfold polynomialHeightDecay
  change X ^ (-(k + 3 : ℤ)) ≤ X ^ (-(l + 3 : ℤ))
  exact zpow_le_zpow_right₀ hX_one hexp

/-- The `tsum` over one exact-height fiber is the corresponding finite shell sum. -/
theorem tsum_heightFiber_polynomialHeightDecay_eq_shellSum
    (k m : ℕ) :
    (∑' x : heightFiber m, polynomialHeightDecay k x.1) =
      polynomialHeightShellSum k m := by
  have htsum :
      (∑' x : heightFiber m, polynomialHeightDecay k x.1) =
        ∑ x : heightFiber m, polynomialHeightDecay k x.1 :=
    tsum_fintype (fun x : heightFiber m => polynomialHeightDecay k x.1)
  have huniv :
      (∑ x : heightFiber m, polynomialHeightDecay k x.1) =
        ∑ x in (heightShell m).attach, polynomialHeightDecay k x.1 := by
    exact congrArg
      (fun s : Finset (heightFiber m) =>
        ∑ x in s, polynomialHeightDecay k x.1)
      (Finset.univ_eq_attach (heightShell m))
  have hattach :
      (∑ x in (heightShell m).attach, polynomialHeightDecay k x.1) =
        ∑ ι in heightShell m, polynomialHeightDecay k ι :=
    Finset.sum_attach
      (heightShell m)
      (fun ι : ZetaPrimePowerIndex => polynomialHeightDecay k ι)
  unfold polynomialHeightShellSum
  exact htsum.trans (huniv.trans hattach)

/-- Raw indices map constructively to their exact rectangular-height fiber. -/
def toHeightFiberSigma
    (ι : ZetaPrimePowerIndex) :
    Sigma heightFiber :=
  ⟨ι.height, ⟨ι, (mem_heightShell_iff ι.height ι).mpr rfl⟩⟩

/-- A point of a height fiber forgets to its raw prime-power index. -/
def ofHeightFiberSigma
    (s : Sigma heightFiber) : ZetaPrimePowerIndex :=
  s.2.1

/-- Forgetting after height-fiber decomposition returns the original raw index. -/
theorem ofHeightFiberSigma_toHeightFiberSigma
    (ι : ZetaPrimePowerIndex) :
    ofHeightFiberSigma (toHeightFiberSigma ι) = ι := by
  rfl

/-- Height-fiber decomposition after forgetting is the original height-fiber point. -/
theorem toHeightFiberSigma_ofHeightFiberSigma
    (s : Sigma heightFiber) :
    toHeightFiberSigma (ofHeightFiberSigma s) = s := by
  rcases s with ⟨m, x⟩
  rcases x with ⟨ι, hι⟩
  have hheight : ι.height = m :=
    (mem_heightShell_iff m ι).mp hι
  cases hheight
  rfl

/-- The constructive equivalence between raw indices and their height-fiber decomposition. -/
def heightFiberSigmaEquiv :
    ZetaPrimePowerIndex ≃ Sigma heightFiber where
  toFun := toHeightFiberSigma
  invFun := ofHeightFiberSigma
  left_inv := ofHeightFiberSigma_toHeightFiberSigma
  right_inv := toHeightFiberSigma_ofHeightFiberSigma

/-- Summability over exact-height fibers transports to summability over raw indices. -/
theorem summable_polynomialHeightDecay_of_heightFiberSummability
    (k : ℕ)
    (hshellSum : Summable (fun m : ℕ => polynomialHeightShellSum k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  have hsigma :
      Summable
        (fun s : Sigma heightFiber =>
          polynomialHeightDecay k (ofHeightFiberSigma s)) := by
    refine (summable_sigma_of_nonneg ?_).mpr ?_
    · intro s
      exact polynomialHeightDecay_nonnegative k (ofHeightFiberSigma s)
    · constructor
      · intro m
        exact (hasSum_fintype
          (fun x : heightFiber m => polynomialHeightDecay k x.1)).summable
      · have hfiberSums :
            (fun m : ℕ =>
              ∑' x : heightFiber m,
                polynomialHeightDecay k x.1) =
              fun m : ℕ => polynomialHeightShellSum k m := by
          funext m
          exact tsum_heightFiber_polynomialHeightDecay_eq_shellSum k m
        exact Eq.subst
          (motive := fun u : ℕ → ℝ => Summable u)
          hfiberSums.symm
          hshellSum
  exact ((heightFiberSigmaEquiv.symm).summable_iff).mp hsigma

/-- Summability of exact-height shell sums transports to summability over raw indices. -/
theorem summable_polynomialHeightDecay_of_shellSums
    (k : ℕ)
    (hshellSum : Summable (fun m : ℕ => polynomialHeightShellSum k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_heightFiberSummability k hshellSum

/-- Rectangular-height decay is summable once the height-shell masses are summable.

This is the shell-counting transport theorem from the two-dimensional raw prime-power
index to the one-dimensional height majorant. -/
theorem summable_polynomialHeightDecay_of_shellMass
    (k : ℕ)
    (hshell : Summable (fun m : ℕ => polynomialHeightShellMass k m)) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_shellSums
    k
    (summable_polynomialHeightShellSum_of_shellMass k hshell)

/-- Rectangular-height polynomial decay is summable over raw prime-power indices. -/
theorem summable_polynomialHeightDecay
    (k : ℕ) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        polynomialHeightDecay k ι) := by
  exact summable_polynomialHeightDecay_of_shellMass
    k
    (summable_polynomialHeightShellMass k)

/-- Constant multiples of rectangular prime-power polynomial height decay are summable.

This is the combinatorial owner theorem behind contour-localization majorants.  The
exponent has two spare powers because the raw prime-power index is a rectangular
two-dimensional coordinate. -/
theorem summable_const_mul_polynomialHeightDecay
    (C : ℝ) (k : ℕ) :
    Summable
      (fun ι : ZetaPrimePowerIndex =>
        C * polynomialHeightDecay k ι) := by
  exact (summable_polynomialHeightDecay k).mul_left C

/-- The completed explicit-formula prime-power weight. -/
def weight (ι : ZetaPrimePowerIndex) : ℝ :=
  if _hp : Nat.Prime ι.p then
    if _hn : 1 ≤ ι.n then
      Real.log ι.p / Real.sqrt (ι.p ^ ι.n)
    else
      0
  else
    0

/-- The square-root prime-power weight used in translation-defect packets. -/
def sqrtWeight (ι : ZetaPrimePowerIndex) : ℝ :=
  Real.sqrt (weight ι)

/-- A bounded finite window of genuine prime-power indices.  The natural bound is the owner
finite approximation; analytic cutoff statements can later compare it with a real logarithmic
height. -/
def window (N : ℕ) : Finset ZetaPrimePowerIndex :=
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
    (fun q : ℕ × ℕ => Nat.Prime q.1 ∧ 1 ≤ q.2)
    |>.map
      ⟨fun q => ⟨q.1, q.2⟩, by
        intro q r hqr
        cases q
        cases r
        cases hqr
        rfl⟩

/-- The unfiltered rectangular box of prime-power coordinates.  Unlike `window`, this exhausts
all raw indices and is the correct object for generic `HasSum`/`tsum` exhaustion. -/
def box (N : ℕ) : Finset ZetaPrimePowerIndex :=
  rawBox N

theorem mem_box_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ box N ↔ ι.p < N + 1 ∧ ι.n < N + 1 := by
  unfold box
  exact mem_rawBox_iff N ι

/-- Rectangular raw prime-power boxes are monotone in the cutoff. -/
theorem box_mono {N M : ℕ} (hNM : N ≤ M) :
    box N ⊆ box M := by
  intro ι hι
  have hmem := (mem_box_iff N ι).mp hι
  have hp : ι.p < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.1) hNM)
  have hn : ι.n < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.2) hNM)
  exact (mem_box_iff M ι).mpr ⟨hp, hn⟩

/-- Rectangular raw prime-power boxes exhaust all raw prime-power coordinates. -/
theorem box_tendsto_atTop :
    Filter.Tendsto box Filter.atTop Filter.atTop := by
  exact Monotone.tendsto_atTop_finset
    (fun N M hNM => box_mono hNM)
    (fun ι : ZetaPrimePowerIndex =>
      ⟨max ι.p ι.n, by
        refine (mem_box_iff (max ι.p ι.n) ι).mpr ?_
        have hp_le : ι.p ≤ max ι.p ι.n := Nat.le_max_left ι.p ι.n
        have hn_le : ι.n ≤ max ι.p ι.n := Nat.le_max_right ι.p ι.n
        exact ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩⟩)

theorem mem_window_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N ↔ ι.p < N + 1 ∧ ι.n < N + 1 ∧ Nat.Prime ι.p ∧ 1 ≤ ι.n := by
  constructor
  · intro hι
    unfold window at hι
    rcases Finset.mem_map.mp hι with ⟨q, hq, hqι⟩
    rcases q with ⟨p, n⟩
    have hpair :
        (p, n) ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)) ∧
          Nat.Prime p ∧ 1 ≤ n := by
      exact Finset.mem_filter.mp hq
    have hp : p < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hpair.1).1
    have hn : n < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hpair.1).2
    cases hqι
    exact ⟨hp, hn, hpair.2.1, hpair.2.2⟩
  · intro hι
    unfold window
    refine Finset.mem_map.mpr ?_
    refine ⟨(ι.p, ι.n), ?_, rfl⟩
    refine Finset.mem_filter.mpr ?_
    exact
      ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hι.1, Finset.mem_range.mpr hι.2.1⟩,
        hι.2.2.1, hι.2.2.2⟩

/-- The genuine prime-power window is the genuine part of the rectangular box. -/
theorem mem_window_iff_mem_box_and_isGenuine (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N ↔ ι ∈ box N ∧ IsGenuine ι := by
  constructor
  · intro hι
    have hmem := (mem_window_iff N ι).mp hι
    exact ⟨(mem_box_iff N ι).mpr ⟨hmem.1, hmem.2.1⟩,
      ⟨hmem.2.2.1, hmem.2.2.2⟩⟩
  · intro hι
    have hbox := (mem_box_iff N ι).mp hι.1
    exact (mem_window_iff N ι).mpr
      ⟨hbox.1, hbox.2, hι.2.1, hι.2.2⟩

/-- Summing a function that vanishes on nongenuine indices over the rectangular box is the
same as summing it over the genuine prime-power window. -/
theorem sum_box_eq_sum_window_of_zero_not_isGenuine
    {A : Type*} [AddCommMonoid A]
    (a : ZetaPrimePowerIndex → A)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → a ι = 0)
    (N : ℕ) :
    ∑ ι in box N, a ι = ∑ ι in window N, a ι := by
  have hsubset : window N ⊆ box N := by
    intro ι hι
    exact ((mem_window_iff_mem_box_and_isGenuine N ι).mp hι).1
  have hsum :
      ∑ ι in window N, a ι = ∑ ι in box N, a ι := by
    exact Finset.sum_subset hsubset
      (fun ι hbox hnot_window => by
        have hnot_genuine : ¬ IsGenuine ι := by
          intro hgenuine
          exact hnot_window
            ((mem_window_iff_mem_box_and_isGenuine N ι).mpr ⟨hbox, hgenuine⟩)
        exact hzero ι hnot_genuine)
  exact hsum.symm

/-- Summable raw prime-power families are exhausted by rectangular boxes. -/
theorem tendsto_sum_box_tsum_of_summable
    (a : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable a) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in box N, a ι)
      Filter.atTop
      (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) := by
  exact hsum.hasSum.comp box_tendsto_atTop

/-- Summable families that vanish on nongenuine prime-power indices are exhausted by genuine
prime-power windows. -/
theorem tendsto_sum_window_tsum_of_summable
    (a : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable a)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → a ι = 0) :
    Filter.Tendsto
      (fun N : ℕ => ∑ ι in window N, a ι)
      Filter.atTop
      (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) := by
  have hbox :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in box N, a ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, a ι)) :=
    tendsto_sum_box_tsum_of_summable a hsum
  have hfun :
      (fun N : ℕ => ∑ ι in box N, a ι) =
        (fun N : ℕ => ∑ ι in window N, a ι) := by
    funext N
    exact sum_box_eq_sum_window_of_zero_not_isGenuine a hzero N
  exact Eq.subst
    (motive := fun u : ℕ → ℝ =>
      Filter.Tendsto u Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, a ι)))
    hfun
    hbox

/-- The finite window part of a prime-power family. -/
noncomputable def windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    ZetaPrimePowerIndex → ℝ :=
  fun ι =>
    if ι ∈ window N then
      u ι
    else
      0

/-- The outside-window tail part of a prime-power family. -/
noncomputable def spectralTail
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    ZetaPrimePowerIndex → ℝ :=
  fun ι =>
    if ι ∈ window N then
      0
    else
      u ι

/-- The finite window part and outside-window tail reconstruct the original family
coordinatewise. -/
theorem windowPart_add_spectralTail_apply
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) (ι : ZetaPrimePowerIndex) :
    windowPart u N ι + spectralTail u N ι = u ι := by
  by_cases hι : ι ∈ window N
  · have hleft : windowPart u N ι = u ι := by
      unfold windowPart
      exact if_pos hι
    have hright : spectralTail u N ι = 0 := by
      unfold spectralTail
      exact if_pos hι
    calc
      windowPart u N ι + spectralTail u N ι
          = u ι + spectralTail u N ι := by
              exact congrArg (fun x : ℝ => x + spectralTail u N ι) hleft
      _ = u ι + 0 := by
              exact congrArg (fun x : ℝ => u ι + x) hright
      _ = u ι := by
              exact add_zero (u ι)
  · have hleft : windowPart u N ι = 0 := by
      unfold windowPart
      exact if_neg hι
    have hright : spectralTail u N ι = u ι := by
      unfold spectralTail
      exact if_neg hι
    calc
      windowPart u N ι + spectralTail u N ι
          = 0 + spectralTail u N ι := by
              exact congrArg (fun x : ℝ => x + spectralTail u N ι) hleft
      _ = 0 + u ι := by
              exact congrArg (fun x : ℝ => 0 + x) hright
      _ = u ι := by
              exact zero_add (u ι)

/-- The finite window part and outside-window tail reconstruct the original family. -/
theorem windowPart_add_spectralTail
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    (fun ι : ZetaPrimePowerIndex => windowPart u N ι + spectralTail u N ι) = u := by
  funext ι
  exact windowPart_add_spectralTail_apply u N ι

/-- The outside-window tail is the original family minus its finite window part,
coordinatewise. -/
theorem spectralTail_eq_original_sub_windowPart_apply
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) (ι : ZetaPrimePowerIndex) :
    spectralTail u N ι = u ι - windowPart u N ι := by
  by_cases hι : ι ∈ window N
  · have htail : spectralTail u N ι = 0 := by
      unfold spectralTail
      exact if_pos hι
    have hwindow : windowPart u N ι = u ι := by
      unfold windowPart
      exact if_pos hι
    calc
      spectralTail u N ι
          = 0 := htail
      _ = u ι - u ι := by
              exact (sub_self (u ι)).symm
      _ = u ι - windowPart u N ι := by
              exact congrArg (fun x : ℝ => u ι - x) hwindow.symm
  · have htail : spectralTail u N ι = u ι := by
      unfold spectralTail
      exact if_neg hι
    have hwindow : windowPart u N ι = 0 := by
      unfold windowPart
      exact if_neg hι
    calc
      spectralTail u N ι
          = u ι := htail
      _ = u ι - 0 := by
              exact (sub_zero (u ι)).symm
      _ = u ι - windowPart u N ι := by
              exact congrArg (fun x : ℝ => u ι - x) hwindow.symm

/-- The outside-window tail is the original family minus its finite window part. -/
theorem spectralTail_eq_original_sub_windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    spectralTail u N =
      fun ι : ZetaPrimePowerIndex => u ι - windowPart u N ι := by
  funext ι
  exact spectralTail_eq_original_sub_windowPart_apply u N ι

/-- The finite indicator vanishes off its finite support. -/
theorem finsetIndicator_eq_zero_of_not_mem
    {α : Type*} [DecidableEq α]
    (s : Finset α) (u : α → ℝ) {a : α}
    (ha : a ∉ s) :
    (if a ∈ s then
      u a
    else
      0) = 0 := by
  exact if_neg ha

/-- A function that vanishes off a finset has infinite sum equal to its finite sum over
that finset. -/
theorem hasSum_of_eq_zero_off_finset
    {α : Type*} [DecidableEq α]
    (s : Finset α) (v : α → ℝ)
    (hv : ∀ a : α, a ∉ s → v a = 0) :
    HasSum v (∑ a in s, v a) := by
  exact hasSum_sum_of_ne_finset_zero hv

/-- A real-valued function cut out by a finite indicator has infinite sum equal to the
corresponding finite sum. -/
theorem hasSum_finsetIndicator
    {α : Type*} [DecidableEq α]
    (s : Finset α) (u : α → ℝ) :
    HasSum
      (fun a : α =>
        if a ∈ s then
          u a
        else
          0)
      (∑ a in s, u a) := by
  let v : α → ℝ :=
    fun a : α =>
      if a ∈ s then
        u a
      else
        0
  have hv : ∀ a : α, a ∉ s → v a = 0 := by
    intro a ha
    unfold v
    exact finsetIndicator_eq_zero_of_not_mem s u ha
  have hsum_v : HasSum v (∑ a in s, v a) :=
    hasSum_of_eq_zero_off_finset s v hv
  have hsum_eq :
      (∑ a in s, v a) = ∑ a in s, u a := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    unfold v
    exact if_pos ha
  exact Eq.subst
    (motive := fun x : ℝ => HasSum v x)
    hsum_eq
    hsum_v

/-- The finite window part has sum equal to its finite window sum. -/
theorem windowPart_hasSum_windowSum
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    HasSum (windowPart u N) (∑ ι in window N, u ι) := by
  exact hasSum_finsetIndicator (window N) u

/-- A finite window part is summable. -/
theorem summable_windowPart
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    Summable (windowPart u N) := by
  exact (windowPart_hasSum_windowSum u N).summable

/-- The finite window part has `tsum` equal to its finite window sum. -/
theorem windowPart_tsum_eq_windowSum
    (u : ZetaPrimePowerIndex → ℝ) (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) =
      ∑ ι in window N, u ι := by
  exact (windowPart_hasSum_windowSum u N).tsum_eq

/-- The outside-window tail of a summable family is summable. -/
theorem summable_spectralTail_of_summable
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    Summable (spectralTail u N) := by
  have hwindow : Summable (windowPart u N) :=
    summable_windowPart u N
  have hsub :
      Summable (fun ι : ZetaPrimePowerIndex => u ι - windowPart u N ι) :=
    hsum.sub hwindow
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ => Summable v)
    (spectralTail_eq_original_sub_windowPart u N).symm
    hsub

/-- The `tsum` of a summable family splits into its finite window part and its
outside-window tail. -/
theorem tsum_eq_windowPart_tsum_add_spectralTail_tsum
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex, u ι) =
      (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
        (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) := by
  have hwindow : Summable (windowPart u N) :=
    summable_windowPart u N
  have htail : Summable (spectralTail u N) :=
    summable_spectralTail_of_summable u hsum N
  have hsplit :
      (∑' ι : ZetaPrimePowerIndex,
        (windowPart u N ι + spectralTail u N ι)) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) :=
    tsum_add hwindow htail
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ =>
      (∑' ι : ZetaPrimePowerIndex, v ι) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι))
    (windowPart_add_spectralTail u N)
    hsplit

/-- The complement tail of a summable prime-window family is the total `tsum` minus the
finite window sum. -/
theorem spectralTail_eq_tsum_sub_windowSum
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (N : ℕ) :
    (∑' ι : ZetaPrimePowerIndex,
      if ι ∈ window N then
        0
      else
        u ι) =
      (∑' ι : ZetaPrimePowerIndex, u ι) -
        ∑ ι in window N, u ι := by
  have hsplit :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) :=
    tsum_eq_windowPart_tsum_add_spectralTail_tsum u hsum N
  have hwindow :
      (∑' ι : ZetaPrimePowerIndex, windowPart u N ι) =
        ∑ ι in window N, u ι :=
    windowPart_tsum_eq_windowSum u N
  have htail_fun :
      (fun ι : ZetaPrimePowerIndex =>
        if ι ∈ window N then
          0
        else
          u ι) =
        spectralTail u N := by
    funext ι
    rfl
  have htotal :
      (∑' ι : ZetaPrimePowerIndex, u ι) =
        (∑ ι in window N, u ι) +
          (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) := by
    exact hsplit.trans
      (congrArg
        (fun x : ℝ =>
          x + (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι))
        hwindow)
  have htail :
      (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) -
          ∑ ι in window N, u ι := by
    calc
      (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)
          = ((∑ ι in window N, u ι) +
              (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)) -
              ∑ ι in window N, u ι := by
              exact (add_sub_cancel_left
                (∑ ι in window N, u ι)
                (∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)).symm
      _ = (∑' ι : ZetaPrimePowerIndex, u ι) -
              ∑ ι in window N, u ι := by
              exact congrArg
                (fun x : ℝ => x - ∑ ι in window N, u ι)
                htotal.symm
  exact Eq.subst
    (motive := fun v : ZetaPrimePowerIndex → ℝ =>
      (∑' ι : ZetaPrimePowerIndex, v ι) =
        (∑' ι : ZetaPrimePowerIndex, u ι) -
          ∑ ι in window N, u ι)
    htail_fun.symm
    htail

/-- The outside-window tail sum of a summable prime-power family vanishes along the
prime-power windows. -/
theorem spectralTail_tsum_tendsto_zero_of_summable
    (u : ZetaPrimePowerIndex → ℝ)
    (hsum : Summable u)
    (hzero : ∀ ι : ZetaPrimePowerIndex, ¬ IsGenuine ι → u ι = 0) :
    Filter.Tendsto
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)
      Filter.atTop
      (nhds 0) := by
  have hwindow :
      Filter.Tendsto
        (fun N : ℕ => ∑ ι in window N, u ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    tendsto_sum_window_tsum_of_summable u hsum hzero
  have hconstant :
      Filter.Tendsto
        (fun _N : ℕ => ∑' ι : ZetaPrimePowerIndex, u ι)
        Filter.atTop
        (nhds (∑' ι : ZetaPrimePowerIndex, u ι)) :=
    tendsto_const_nhds
  have hsub :
      Filter.Tendsto
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in window N, u ι)
        Filter.atTop
        (nhds
          ((∑' ι : ZetaPrimePowerIndex, u ι) -
            (∑' ι : ZetaPrimePowerIndex, u ι))) :=
    hconstant.sub hwindow
  have htarget :
      (∑' ι : ZetaPrimePowerIndex, u ι) -
          (∑' ι : ZetaPrimePowerIndex, u ι) =
        0 :=
    sub_self (∑' ι : ZetaPrimePowerIndex, u ι)
  have htail_fun :
      (fun N : ℕ =>
        ∑' ι : ZetaPrimePowerIndex, spectralTail u N ι) =
        (fun N : ℕ =>
          (∑' ι : ZetaPrimePowerIndex, u ι) -
            ∑ ι in window N, u ι) := by
    funext N
    exact spectralTail_eq_tsum_sub_windowSum u hsum N
  exact Eq.subst
    (motive := fun v : ℕ → ℝ =>
      Filter.Tendsto v Filter.atTop (nhds 0))
    htail_fun.symm
    (Eq.subst
      (motive := fun x : ℝ =>
        Filter.Tendsto
          (fun N : ℕ =>
            (∑' ι : ZetaPrimePowerIndex, u ι) -
              ∑ ι in window N, u ι)
          Filter.atTop
          (nhds x))
      htarget
      hsub)

/-- A summable real tail is bounded by a nonnegative summable majorant tail when each
coordinate norm is bounded by the majorant. -/
theorem norm_spectralTail_tsum_le_spectralTail_tsum_of_norm_le
    (u v : ZetaPrimePowerIndex → ℝ)
    (hv : Summable v)
    (hbound : ∀ ι : ZetaPrimePowerIndex, ‖u ι‖ ≤ v ι)
    (N : ℕ) :
    ‖(∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)‖ ≤
      ∑' ι : ZetaPrimePowerIndex, spectralTail v N ι := by
  have htail_v : Summable (spectralTail v N) :=
    summable_spectralTail_of_summable v hv N
  have hpoint :
      ∀ ι : ZetaPrimePowerIndex,
        ‖spectralTail u N ι‖ ≤ spectralTail v N ι := by
    intro ι
    by_cases hι : ι ∈ window N
    · have hu_zero : spectralTail u N ι = 0 := by
        unfold spectralTail
        exact if_pos hι
      have hv_zero : spectralTail v N ι = 0 := by
        unfold spectralTail
        exact if_pos hι
      calc
        ‖spectralTail u N ι‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm hu_zero
        _ = 0 := by
          exact norm_zero
        _ ≤ spectralTail v N ι := by
          exact le_of_eq hv_zero.symm
    · have hu_value : spectralTail u N ι = u ι := by
        unfold spectralTail
        exact if_neg hι
      have hv_value : spectralTail v N ι = v ι := by
        unfold spectralTail
        exact if_neg hι
      calc
        ‖spectralTail u N ι‖ = ‖u ι‖ := by
          exact congrArg norm hu_value
        _ ≤ v ι := hbound ι
        _ = spectralTail v N ι := by
          exact hv_value.symm
  have htail_u_norm :
      Summable (fun ι : ZetaPrimePowerIndex => ‖spectralTail u N ι‖) := by
    refine Summable.of_norm_bounded (spectralTail v N) htail_v ?_
    intro ι
    calc
      ‖‖spectralTail u N ι‖‖ = ‖spectralTail u N ι‖ := by
        exact norm_norm (spectralTail u N ι)
      _ ≤ spectralTail v N ι := hpoint ι
  have hnorm_tsum :
      ‖(∑' ι : ZetaPrimePowerIndex, spectralTail u N ι)‖ ≤
        ∑' ι : ZetaPrimePowerIndex, ‖spectralTail u N ι‖ :=
    norm_tsum_le_tsum_norm htail_u_norm
  have hmajorant_tsum :
      (∑' ι : ZetaPrimePowerIndex, ‖spectralTail u N ι‖) ≤
        ∑' ι : ZetaPrimePowerIndex, spectralTail v N ι :=
    tsum_le_tsum hpoint htail_u_norm htail_v
  exact hnorm_tsum.trans hmajorant_tsum

/-- Membership in a prime-power window exposes genuine prime-power data. -/
theorem isGenuine_of_mem_window
    (N : ℕ) (ι : ZetaPrimePowerIndex) (hι : ι ∈ window N) :
    IsGenuine ι := by
  have hmem := (mem_window_iff N ι).mp hι
  exact ⟨hmem.2.2.1, hmem.2.2.2⟩

/-- Prime-power windows are monotone in the natural cutoff. -/
theorem window_mono {N M : ℕ} (hNM : N ≤ M) :
    window N ⊆ window M := by
  intro ι hι
  have hmem := (mem_window_iff N ι).mp hι
  refine (mem_window_iff M ι).mpr ?_
  have hp : ι.p < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.1) hNM)
  have hn : ι.n < M + 1 := Nat.lt_succ_of_le (le_trans (Nat.le_of_lt_succ hmem.2.1) hNM)
  exact ⟨hp, hn, hmem.2.2.1, hmem.2.2.2⟩

/-- A genuine prime-power index eventually belongs to every sufficiently large rectangular
prime-power window. -/
theorem eventually_mem_window_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    ∀ᶠ N : ℕ in Filter.atTop, ι ∈ window N := by
  refine Filter.eventually_atTop.2 ?_
  refine ⟨max ι.p ι.n, ?_⟩
  intro N hN
  refine (mem_window_iff N ι).mpr ?_
  have hp_le : ι.p ≤ N := le_trans (Nat.le_max_left ι.p ι.n) hN
  have hn_le : ι.n ≤ N := le_trans (Nat.le_max_right ι.p ι.n) hN
  have hp_lt : ι.p < N + 1 := Nat.lt_succ_of_le hp_le
  have hn_lt : ι.n < N + 1 := Nat.lt_succ_of_le hn_le
  exact ⟨hp_lt, hn_lt, hι.1, hι.2⟩

/-- Every prime-power index that belongs to a window is genuine. -/
theorem mem_window_isGenuine
    (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ window N → IsGenuine ι := by
  intro hι
  exact isGenuine_of_mem_window N ι hι

/-- The natural number `1` is at most `2`. -/
theorem one_le_two_nat : (1 : ℕ) ≤ 2 :=
  Nat.succ_le_succ (Nat.zero_le 1)

/-- The natural number `0` is strictly less than `2`. -/
theorem zero_lt_two_nat : (0 : ℕ) < 2 :=
  Nat.lt.step Nat.zero_lt_one

/-- The real number `1` is strictly less than `2`. -/
theorem one_lt_two_real : (1 : ℝ) < 2 :=
  one_lt_two

/-- The real number `2` is positive. -/
theorem zero_lt_two_real : (0 : ℝ) < 2 :=
  lt_trans zero_lt_one one_lt_two_real

/-- Genuine prime-power centers are nonnegative. -/
theorem center_nonnegative_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    0 ≤ center ι := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast le_trans one_le_two_nat hp_two
  have hn_nonneg : 0 ≤ (ι.n : ℝ) := Nat.cast_nonneg ι.n
  have hlog_nonneg : 0 ≤ Real.log (ι.p : ℝ) := Real.log_nonneg hp_one_real
  unfold center
  unfold zetaPrimePacketCenter
  exact mul_nonneg hn_nonneg hlog_nonneg

/-- A genuine prime-power center bounded by `B` bounds the prime coordinate by `exp B`. -/
theorem prime_le_exp_of_isGenuine_center_le
    (B : ℝ) (ι : ZetaPrimePowerIndex)
    (hι : IsGenuine ι) (hcenter : center ι ≤ B) :
    (ι.p : ℝ) ≤ Real.exp B := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    exact_mod_cast hp_pos_nat
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (ι.p : ℝ) := Real.log_nonneg hp_one_real
  have hn_one : (1 : ℝ) ≤ ι.n := by
    exact_mod_cast hι.2
  have hlog_le_center : Real.log (ι.p : ℝ) ≤ center ι := by
    unfold center
    unfold zetaPrimePacketCenter
    calc
      Real.log (ι.p : ℝ) = (1 : ℝ) * Real.log (ι.p : ℝ) := by
        exact (one_mul (Real.log (ι.p : ℝ))).symm
      _ ≤ (ι.n : ℝ) * Real.log (ι.p : ℝ) := by
        exact mul_le_mul_of_nonneg_right hn_one hlog_nonneg
  have hlog_le_B : Real.log (ι.p : ℝ) ≤ B := le_trans hlog_le_center hcenter
  exact (Real.log_le_iff_le_exp hp_pos_real).mp hlog_le_B

/-- A genuine prime-power center bounded by `B` bounds the exponent coordinate by
`B / log 2`. -/
theorem exponent_le_div_log_two_of_isGenuine_center_le
    (B : ℝ) (ι : ZetaPrimePowerIndex)
    (hι : IsGenuine ι) (hcenter : center ι ≤ B) :
    (ι.n : ℝ) ≤ B / Real.log 2 := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos one_lt_two_real
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
    exact_mod_cast hp_pos_nat
  have htwo_pos : 0 < (2 : ℝ) := zero_lt_two_real
  have htwo_le_p : (2 : ℝ) ≤ ι.p := by
    exact_mod_cast hp_two
  have hlog_two_le_log_p : Real.log (2 : ℝ) ≤ Real.log (ι.p : ℝ) := by
    exact Real.log_le_log htwo_pos htwo_le_p
  have hn_nonneg : 0 ≤ (ι.n : ℝ) := Nat.cast_nonneg ι.n
  have hn_log_two_le_center :
      (ι.n : ℝ) * Real.log 2 ≤ center ι := by
    unfold center
    unfold zetaPrimePacketCenter
    exact mul_le_mul_of_nonneg_left hlog_two_le_log_p hn_nonneg
  have hn_log_two_le_B : (ι.n : ℝ) * Real.log 2 ≤ B :=
    le_trans hn_log_two_le_center hcenter
  exact (le_div_iff₀ hlog_two_pos).mpr hn_log_two_le_B

/-- Bounded genuine prime-power centers are contained in one rectangular raw box. -/
theorem exists_box_bound_of_isGenuine_center_le
    (B : ℝ) :
    ∃ N : ℕ, ∀ ι : ZetaPrimePowerIndex,
      IsGenuine ι → center ι ≤ B → ι ∈ box N := by
  by_cases hB : 0 ≤ B
  · obtain ⟨Np, hNp⟩ := exists_nat_ge (Real.exp B)
    obtain ⟨Nn, hNn⟩ := exists_nat_ge (B / Real.log 2)
    refine ⟨max Np Nn, ?_⟩
    intro ι hι hcenter
    have hp_exp : (ι.p : ℝ) ≤ Real.exp B :=
      prime_le_exp_of_isGenuine_center_le B ι hι hcenter
    have hn_div : (ι.n : ℝ) ≤ B / Real.log 2 :=
      exponent_le_div_log_two_of_isGenuine_center_le B ι hι hcenter
    have hp_le_Np_real : (ι.p : ℝ) ≤ Np := le_trans hp_exp hNp
    have hn_le_Nn_real : (ι.n : ℝ) ≤ Nn := le_trans hn_div hNn
    have hp_le_Np : ι.p ≤ Np := by
      exact_mod_cast hp_le_Np_real
    have hn_le_Nn : ι.n ≤ Nn := by
      exact_mod_cast hn_le_Nn_real
    have hp_le : ι.p ≤ max Np Nn :=
      le_trans hp_le_Np (Nat.le_max_left Np Nn)
    have hn_le : ι.n ≤ max Np Nn :=
      le_trans hn_le_Nn (Nat.le_max_right Np Nn)
    exact (mem_box_iff (max Np Nn) ι).mpr
      ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩
  · refine ⟨0, ?_⟩
    intro ι hι hcenter
    have hcenter_nonneg : 0 ≤ center ι :=
      center_nonnegative_of_isGenuine ι hι
    have hBlt : B < 0 := lt_of_not_ge hB
    have hcenter_lt_zero : center ι < 0 := lt_of_le_of_lt hcenter hBlt
    exact False.elim ((not_lt_of_ge hcenter_nonneg) hcenter_lt_zero)

/-- The set of genuine prime-power indices with bounded center is finite. -/
theorem finite_setOf_isGenuine_and_center_le
    (B : ℝ) :
    ({ι : ZetaPrimePowerIndex | IsGenuine ι ∧ center ι ≤ B} : Set ZetaPrimePowerIndex).Finite := by
  obtain ⟨N, hN⟩ := exists_box_bound_of_isGenuine_center_le B
  exact Set.Finite.subset (Finset.finite_toSet (box N))
    (fun ι hι => hN ι hι.1 hι.2)

/-- Genuine prime-power weights are nonnegative. -/
theorem weight_nonnegative (ι : ZetaPrimePowerIndex) :
    0 ≤ weight ι := by
  by_cases hp : Nat.Prime ι.p
  · by_cases hn : 1 ≤ ι.n
    · have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hp
      have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le zero_lt_two_nat hp_two
      have hp_one_real : (1 : ℝ) ≤ ι.p := by exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
      have hlog : 0 ≤ Real.log ι.p := Real.log_nonneg hp_one_real
      have hsqrt : 0 ≤ Real.sqrt (ι.p ^ ι.n) := Real.sqrt_nonneg _
      have hnonneg : 0 ≤ Real.log ι.p / Real.sqrt (ι.p ^ ι.n) :=
        div_nonneg hlog hsqrt
      have hweight :
          weight ι = Real.log ι.p / Real.sqrt (ι.p ^ ι.n) := by
        unfold weight
        exact (if_pos hp).trans (if_pos hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        hnonneg
    · have hweight : weight ι = 0 := by
        unfold weight
        exact (if_pos hp).trans (if_neg hn)
      exact Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        hweight.symm
        (le_refl 0)
  · have hweight : weight ι = 0 := by
      unfold weight
      exact if_neg hp
    exact Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hweight.symm
      (le_refl 0)

/-- The real prime-power logarithmic quotient is nonnegative on genuine parameters. -/
theorem real_log_div_sqrt_primePower_nonnegative
    {p n : ℕ} (hp : Nat.Prime p) (_hn : 1 ≤ n) :
    0 ≤ Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_one_real : (1 : ℝ) ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hlog_nonneg : 0 ≤ Real.log (p : ℝ) :=
    Real.log_nonneg hp_one_real
  have hsqrt_nonneg : 0 ≤ Real.sqrt (p ^ n : ℝ) :=
    Real.sqrt_nonneg (p ^ n : ℝ)
  exact div_nonneg hlog_nonneg hsqrt_nonneg

/-- The elementary logarithmic estimate at exponent `1 / 2`, in square-root form. -/
theorem real_log_natCast_le_two_sqrt (p : ℕ) :
    Real.log (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p : ℝ) := by
  have hhalf_pos : 0 < (1 / 2 : ℝ) :=
    div_pos zero_lt_one zero_lt_two
  have hlog :
      Real.log (p : ℝ) ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
    Real.log_natCast_le_rpow_div p hhalf_pos
  have hhalf :
      (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
        (2 : ℝ) * Real.sqrt (p : ℝ) := by
    have htwo_ne_zero : (2 : ℝ) ≠ 0 := two_ne_zero
    have hhalf_mul_two : (1 / 2 : ℝ) * 2 = 1 := by
      exact Eq.trans
        (congrArg (fun x : ℝ => x * 2) (one_div 2))
        (inv_mul_cancel₀ htwo_ne_zero)
    have hhalf_inv : (1 / 2 : ℝ)⁻¹ = 2 :=
      inv_eq_of_mul_eq_one_right hhalf_mul_two
    calc
      (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) =
          (p : ℝ) ^ (1 / 2 : ℝ) * (1 / 2 : ℝ)⁻¹ := by
        exact div_eq_mul_inv ((p : ℝ) ^ (1 / 2 : ℝ)) (1 / 2 : ℝ)
      _ = (p : ℝ) ^ (1 / 2 : ℝ) * 2 := by
        exact congrArg (fun x : ℝ => (p : ℝ) ^ (1 / 2 : ℝ) * x) hhalf_inv
      _ = 2 * (p : ℝ) ^ (1 / 2 : ℝ) := by
        exact mul_comm ((p : ℝ) ^ (1 / 2 : ℝ)) 2
      _ = (2 : ℝ) * Real.sqrt (p : ℝ) := by
        exact congrArg (fun x : ℝ => (2 : ℝ) * x)
          (Real.sqrt_eq_rpow (p : ℝ)).symm
  exact hlog.trans (le_of_eq hhalf)

/-- The square-root denominator increases when a genuine prime is raised to a positive power. -/
theorem real_sqrt_natCast_le_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.sqrt (p : ℝ) ≤ Real.sqrt (p ^ n : ℝ) := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_one_real : (1 : ℝ) ≤ p := by
    exact_mod_cast Nat.succ_le_of_lt hp_pos_nat
  have hn_pos : 0 < n := hn
  have hp_le_pow : (p : ℝ) ≤ (p : ℝ) ^ n :=
    le_self_pow₀ hp_one_real hn_pos.ne'
  have hp_pow_cast : ((p : ℝ) ^ n) = (p ^ n : ℝ) := by
    exact_mod_cast (rfl : p ^ n = p ^ n)
  exact (Real.sqrt_le_sqrt hp_le_pow).trans_eq (congrArg Real.sqrt hp_pow_cast)

/-- The doubled square-root numerator is bounded by the prime-power denominator version. -/
theorem real_two_mul_sqrt_natCast_le_two_mul_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    (2 : ℝ) * Real.sqrt (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p ^ n : ℝ) := by
  exact mul_le_mul_of_nonneg_left
    (real_sqrt_natCast_le_sqrt_primePower hp hn)
    zero_le_two

/-- The logarithm is bounded by twice the prime-power square-root denominator. -/
theorem real_log_natCast_le_two_mul_sqrt_primePower
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.log (p : ℝ) ≤ (2 : ℝ) * Real.sqrt (p ^ n : ℝ) := by
  exact (real_log_natCast_le_two_sqrt p).trans
    (real_two_mul_sqrt_natCast_le_two_mul_sqrt_primePower hp hn)

/-- The real prime-power logarithmic quotient is bounded by two on genuine parameters. -/
theorem real_log_div_sqrt_primePower_le_two
    {p n : ℕ} (hp : Nat.Prime p) (hn : 1 ≤ n) :
    Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) ≤ 2 := by
  have hp_two : 2 ≤ p := Nat.Prime.two_le hp
  have hp_pos_nat : 0 < p := lt_of_lt_of_le zero_lt_two_nat hp_two
  have hp_pow_pos_nat : 0 < p ^ n := pow_pos hp_pos_nat n
  have hp_pow_pos_real : 0 < (p ^ n : ℝ) := by
    exact_mod_cast hp_pow_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (p ^ n : ℝ) :=
    Real.sqrt_pos.mpr hp_pow_pos_real
  exact (div_le_iff₀ hsqrt_pos).mpr
    (real_log_natCast_le_two_mul_sqrt_primePower hp hn)

/-- The scalar prime-power logarithmic weight is globally bounded on genuine
prime-power parameters. -/
theorem real_log_div_sqrt_primePower_norm_le_globalConstant :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ p n : ℕ,
          Nat.Prime p →
            1 ≤ n →
              ‖((Real.log p / Real.sqrt (p ^ n) : ℝ) : ℂ)‖ ≤ A := by
  refine ⟨2, zero_le_two, ?_⟩
  intro p n hp hn
  have hquot_nonneg :
      0 ≤ Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) :=
    real_log_div_sqrt_primePower_nonnegative hp hn
  have hquot_le_two :
      Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) ≤ 2 := by
    exact real_log_div_sqrt_primePower_le_two hp hn
  have hnorm_real :
      ‖((Real.log p / Real.sqrt (p ^ n) : ℝ) : ℂ)‖ =
        Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ) := by
    exact Eq.trans
      (RCLike.norm_ofReal (K := ℂ)
        (Real.log (p : ℝ) / Real.sqrt (p ^ n : ℝ)))
      (abs_of_nonneg hquot_nonneg)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 2)
    hnorm_real.symm
    hquot_le_two

/-- The completed prime-power weight is globally bounded over raw prime-power indices. -/
theorem weight_norm_le_globalConstant :
    ∃ A : ℝ,
      0 ≤ A ∧
        ∀ ι : ZetaPrimePowerIndex, ‖(weight ι : ℂ)‖ ≤ A := by
  obtain ⟨A, hA_nonneg, hA_bound⟩ :=
    real_log_div_sqrt_primePower_norm_le_globalConstant
  refine ⟨A, hA_nonneg, ?_⟩
  intro ι
  by_cases hp : Nat.Prime ι.p
  · by_cases hn : 1 ≤ ι.n
    · have hweight :
          weight ι = Real.log ι.p / Real.sqrt (ι.p ^ ι.n) := by
        unfold weight
        exact (if_pos hp).trans (if_pos hn)
      exact Eq.subst
        (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
        hweight.symm
        (hA_bound ι.p ι.n hp hn)
    · have hweight : weight ι = 0 := by
        unfold weight
        exact (if_pos hp).trans (if_neg hn)
      have hzero : ‖((0 : ℝ) : ℂ)‖ ≤ A := by
        exact Eq.subst
          (motive := fun x : ℝ => x ≤ A)
          (norm_zero : ‖((0 : ℝ) : ℂ)‖ = 0).symm
          hA_nonneg
      exact Eq.subst
        (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
        hweight.symm
        hzero
  · have hweight : weight ι = 0 := by
      unfold weight
      exact if_neg hp
    have hzero : ‖((0 : ℝ) : ℂ)‖ ≤ A := by
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ A)
        (norm_zero : ‖((0 : ℝ) : ℂ)‖ = 0).symm
        hA_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => ‖(x : ℂ)‖ ≤ A)
      hweight.symm
      hzero

/-- Multiplication by the completed prime-power weight is absorbed by increasing the
rectangular-height decay exponent. -/
theorem weight_norm_mul_polynomialHeightDecay_le_shift
    (k : ℕ) :
    ∃ A : ℝ, ∃ l : ℕ,
      0 ≤ A ∧ k ≤ l ∧
        ∀ ι : ZetaPrimePowerIndex,
          ‖(weight ι : ℂ)‖ * polynomialHeightDecay k ι ≤
            A * polynomialHeightDecay l ι := by
  obtain ⟨A, hA_nonneg, hA_bound⟩ := weight_norm_le_globalConstant
  refine ⟨A, k, hA_nonneg, le_refl k, ?_⟩
  intro ι
  have hdecay_nonneg : 0 ≤ polynomialHeightDecay k ι :=
    polynomialHeightDecay_nonnegative k ι
  exact mul_le_mul_of_nonneg_right (hA_bound ι) hdecay_nonneg

/-- Non-genuine prime-power indices have zero completed prime-power weight. -/
theorem weight_eq_zero_of_not_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : ¬ IsGenuine ι) :
    weight ι = 0 := by
  unfold IsGenuine at hι
  unfold weight
  by_cases hp : Nat.Prime ι.p
  · have hn : ¬ 1 ≤ ι.n := by
      intro hn
      exact hι ⟨hp, hn⟩
    exact (if_pos hp).trans (if_neg hn)
  · exact if_neg hp

/-- The square-root weight squares back to the weight. -/
theorem sqrtWeight_mul_self (ι : ZetaPrimePowerIndex) :
    sqrtWeight ι * sqrtWeight ι = weight ι := by
  calc
    sqrtWeight ι * sqrtWeight ι = sqrtWeight ι ^ 2 := by
      exact (pow_two (sqrtWeight ι)).symm
    _ = weight ι := by
      unfold sqrtWeight
      exact Real.sq_sqrt (weight_nonnegative ι)

end ZetaPrimePowerIndex

end
end LFunctions
end Boundary
