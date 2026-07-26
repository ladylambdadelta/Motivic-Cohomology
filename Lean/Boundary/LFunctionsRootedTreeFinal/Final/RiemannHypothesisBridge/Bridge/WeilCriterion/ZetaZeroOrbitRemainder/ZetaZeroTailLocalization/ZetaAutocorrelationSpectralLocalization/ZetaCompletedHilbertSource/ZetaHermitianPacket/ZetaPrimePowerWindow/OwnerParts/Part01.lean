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

namespace ZetaAdmissibleFunction

/-- The display `(p,n)` completed explicit-formula prime weight used by packet coordinates. -/
def zetaCompletedExplicitFormulaPrimeWeight (p n : ℕ) : ℝ :=
  if _hp : Nat.Prime p then
    if _hn : n ≠ 0 then
      Real.log p / Real.sqrt (p ^ n)
    else
      0
  else
    0

end ZetaAdmissibleFunction

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
    exact Finset.mem_map.mpr
      ⟨(ι.p, ι.n),
        Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr hι.1, Finset.mem_range.mpr hι.2⟩,
        rfl⟩

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
    have hp_le : ι.p ≤ m :=
      le_trans (Nat.le_max_left ι.p ι.n) (le_of_eq hheight)
    have hn_le : ι.n ≤ m :=
      le_trans (Nat.le_max_right ι.p ι.n) (le_of_eq hheight)
    have hraw : ι ∈ rawBox m :=
      (mem_rawBox_iff m ι).mpr
        ⟨Nat.lt_succ_of_le hp_le, Nat.lt_succ_of_le hn_le⟩
    exact Finset.mem_filter.mpr ⟨hraw, hheight⟩

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
    exact Finset.mem_map.mpr
      ⟨ι.n, Finset.mem_range.mpr hn_lt,
        by
          cases hp
          rfl⟩
  · intro hι
    unfold heightShellVerticalEdgeModel at hι
    rcases Finset.mem_map.mp hι with ⟨n, hn_range, hn_eq⟩
    cases hn_eq
    unfold heightShellVerticalEdge
    have hraw : ({ p := m, n := n } : ZetaPrimePowerIndex) ∈ rawBox m :=
      (mem_rawBox_iff m ({ p := m, n := n } : ZetaPrimePowerIndex)).mpr
        ⟨Nat.lt_succ_self m, Finset.mem_range.mp hn_range⟩
    exact Finset.mem_filter.mpr ⟨hraw, rfl⟩

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
    exact Finset.mem_map.mpr
      ⟨ι.p, Finset.mem_range.mpr hp_lt,
        by
          cases hn
          rfl⟩
  · intro hι
    unfold heightShellHorizontalEdgeModel at hι
    rcases Finset.mem_map.mp hι with ⟨p, hp_range, hp_eq⟩
    cases hp_eq
    unfold heightShellHorizontalEdge
    have hraw : ({ p := p, n := m } : ZetaPrimePowerIndex) ∈ rawBox m :=
      (mem_rawBox_iff m ({ p := p, n := m } : ZetaPrimePowerIndex)).mpr
        ⟨Finset.mem_range.mp hp_range, Nat.lt_succ_self m⟩
    exact Finset.mem_filter.mpr ⟨hraw, rfl⟩

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


end ZetaPrimePowerIndex

end
end LFunctions
end Boundary
