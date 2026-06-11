import Boundary.LFunctions.ZetaCenteredNormalization
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
  ((Finset.range (N + 1)).product (Finset.range (N + 1))).map
    ⟨fun q => ⟨q.1, q.2⟩, by
      intro q r hqr
      cases q
      cases r
      cases hqr
      rfl⟩

theorem mem_box_iff (N : ℕ) (ι : ZetaPrimePowerIndex) :
    ι ∈ box N ↔ ι.p < N + 1 ∧ ι.n < N + 1 := by
  constructor
  · intro hι
    unfold box at hι
    rcases Finset.mem_map.mp hι with ⟨q, hq, hqι⟩
    rcases q with ⟨p, n⟩
    have hp : p < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hq).1
    have hn : n < N + 1 := by
      exact Finset.mem_range.mp (Finset.mem_product.mp hq).2
    cases hqι
    exact ⟨hp, hn⟩
  · intro hι
    unfold box
    refine Finset.mem_map.mpr ?_
    refine ⟨(ι.p, ι.n), ?_, rfl⟩
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hι.1, Finset.mem_range.mpr hι.2⟩

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
  classical
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

/-- Genuine prime-power centers are nonnegative. -/
theorem center_nonnegative_of_isGenuine
    (ι : ZetaPrimePowerIndex) (hι : IsGenuine ι) :
    0 ≤ center ι := by
  have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hι.1
  have hp_one_real : (1 : ℝ) ≤ ι.p := by
    exact_mod_cast le_trans (by decide : 1 ≤ 2) hp_two
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
  have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le (by decide : 0 < 2) hp_two
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
  have hlog_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hp_pos_real : 0 < (ι.p : ℝ) := by
    have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le (by decide : 0 < 2) hp_two
    exact_mod_cast hp_pos_nat
  have htwo_pos : 0 < (2 : ℝ) := by norm_num
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
  classical
  obtain ⟨N, hN⟩ := exists_box_bound_of_isGenuine_center_le B
  exact Set.Finite.subset (Finset.finite_toSet (box N))
    (fun ι hι => hN ι hι.1 hι.2)

/-- Genuine prime-power weights are nonnegative. -/
theorem weight_nonnegative (ι : ZetaPrimePowerIndex) :
    0 ≤ weight ι := by
  by_cases hp : Nat.Prime ι.p
  · by_cases hn : 1 ≤ ι.n
    · have hp_two : 2 ≤ ι.p := Nat.Prime.two_le hp
      have hp_pos_nat : 0 < ι.p := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hp_two
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
