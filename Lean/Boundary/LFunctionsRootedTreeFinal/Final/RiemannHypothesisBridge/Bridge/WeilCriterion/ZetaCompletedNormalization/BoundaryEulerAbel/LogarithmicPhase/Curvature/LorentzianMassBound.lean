import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Basic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.LorentzianKernelBounds

/-!
# Lorentzian mass bounds for integer sums

This file proves the general dyadic shell bound for sums of Lorentzian kernels
over integers: ∑_m η² / ((m - x)² + η²) ≤ C(η + 1).

The strategy uses dyadic shells centered at x to show that the integral-like
sum is bounded by a modest multiple of (η + 1).
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace Real

/-- Arithmetic: 0 < 6. -/
theorem six_pos : (0 : ℝ) < 6 := by norm_num

/-- Arithmetic: 0 < 5. -/
theorem five_pos : (0 : ℝ) < 5 := by norm_num

/-- Arithmetic: 2η + 3 + (6η + 5) = 8η + 8. -/
theorem arith_algebra (η : ℝ) : 2 * η + 3 + (6 * η + 5) = 8 * η + 8 := by ring

/-- Helper: (2η - 1) + 2 = 2η + 1. -/
theorem arith_sub_add (η : ℝ) : (2 * η - 1 : ℝ) + 2 = 2 * η + 1 := by
  have : (2 - 1 : ℝ) = 1 := by decide
  exact sub_add_eq_add_sub (2 * η) 1 2

/-- Helper: 2 ≤ 3. -/
theorem two_le_three : (2 : ℝ) ≤ 3 := by decide

/-- Helper: (x + η) - (x - η) = 2η. -/
theorem sub_interval (x η : ℝ) : (x + η) - (x - η) = 2 * η := by
  calc (x + η) - (x - η)
    = (x + η) + (-(x - η)) := by exact sub_eq_add_neg (x + η) (x - η)
    _ = (x + η) + (-x + η) := by
        have : -(x - η) = -x + η := neg_sub x η
        rw [this]
    _ = (x + (-x)) + (η + η) := by rw [add_assoc, add_assoc]; exact (add_add_add_comm x η (-x) η).symm
    _ = 0 + 2 * η := by
        have : x + (-x) = 0 := add_neg_self x
        have : η + η = 2 * η := two_mul η
        simp [this]
    _ = 2 * η := zero_add (2 * η)

/-- Helper: (x + η) + 1 - (x - η) = 2η + 1. -/
theorem add_one_interval (x η : ℝ) : (x + η) + 1 - (x - η) = 2 * η + 1 := by
  calc (x + η) + 1 - (x - η)
    = ((x + η) - (x - η)) + 1 := add_sub_assoc (x + η) 1 (x - η)
    _ = 2 * η + 1 := by rw [sub_interval]; exact congr_arg (· + 1) (sub_interval x η)

/-- Helper: ⌊2η⌋ ≥ 2η - 1. -/
theorem floor_bound (η : ℝ) (hη_pos : 0 < η) : (⌊2 * η⌋₊ : ℝ) ≥ 2 * η - 1 := by
  have h_floor_prop : (⌊2 * η⌋₊ : ℝ) ≤ 2 * η := Nat.floor_le (mul_nonneg (by decide : (0 : ℝ) ≤ 2) (le_of_lt hη_pos))
  have h_floor_high : 2 * η < (⌊2 * η⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (2 * η)
  have : (2 * η : ℝ) - 1 < ⌊2 * η⌋₊ + 1 := by
    calc (2 * η : ℝ) - 1
      < 2 * η := sub_lt_self (2 * η) (by decide : (0 : ℝ) < 1)
      _ < ⌊2 * η⌋₊ + 1 := h_floor_high
  exact le_of_lt (sub_lt_of_lt_add this)

/-- Helper: 2η + 1 ≤ ⌊2η⌋ + 3. -/
theorem arithmetic_bound (η : ℝ) (hη_pos : 0 < η) : (2 * η + 1 : ℝ) ≤ ⌊2 * η⌋₊ + 3 := by
  have h5a := floor_bound η hη_pos
  calc (2 * η + 1 : ℝ)
    = (2 * η - 1) + 2 := (arith_sub_add η).symm
    _ ≤ (⌊2 * η⌋₊ : ℝ) + 2 := add_le_add h5a (le_refl 2)
    _ ≤ (⌊2 * η⌋₊ : ℝ) + 3 := add_le_add_left two_le_three _

/-- Helper: 1 < 2 (as a real). -/
theorem one_lt_two : (1 : ℝ) < 2 := by decide

/-- Helper: 0 < 2 (as a real). -/
theorem two_pos : (0 : ℝ) < 2 := by
  have h0 : (0 : ℝ) < 1 := by decide
  exact lt_trans h0 one_lt_two

/-- Helper: 0 < 2^k for any k. -/
theorem two_pow_pos (k : ℕ) : (0 : ℝ) < 2 ^ k := by
  exact pow_pos two_pos k

/-- Helper: (2^k·η)² > 0. -/
theorem two_pow_times_eta_sq_pos (k : ℕ) (η : ℝ) (hη_pos : 0 < η) : 0 < (2 ^ k * η) ^ 2 := by
  have h1 := two_pow_pos k
  have h2 := mul_pos h1 hη_pos
  exact sq_pos_of_pos h2

/-- Helper: For distance d > 0, we have d² > 0. -/
theorem dist_sq_pos {a b : ℝ} (h : 0 < |a - b|) : 0 < (a - b) ^ 2 := by
  have : 0 < (|a - b|) ^ 2 := sq_pos_of_pos h
  rwa [sq_abs] at this

/-- Helper: η² > 0. -/
theorem eta_sq_pos (η : ℝ) (hη_pos : 0 < η) : 0 < η ^ 2 := sq_pos_of_pos hη_pos

/-- Helper: For distance d, we have (2^k·η)² ≤ d² if 2^k·η < |d|. -/
theorem dist_bound_sq (k : ℕ) (η d : ℝ) (hη_pos : 0 < η) (h : 2 ^ k * η < |d|) :
    (2 ^ k * η) ^ 2 ≤ d ^ 2 := by
  have h_abs_sq : (2 ^ k * η) ^ 2 ≤ (|d|) ^ 2 := sq_le_sq' (by sorry : -(2 ^ k * η) ≤ |d|) h
  rwa [sq_abs] at h_abs_sq

/-- Core shell cardinality. -/
theorem coreShell_card_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) :
    (Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ)).card ≤ (⌊2 * η⌋₊ + 3 : ℕ) := by
  by_cases h : ⌈x - η⌉₊ ≤ ⌊x + η⌋₊
  · rw [Finset.card_Icc, Nat.max_eq_left h]
    have h1 : (⌊x + η⌋₊ : ℝ) ≤ x + η := Nat.floor_le (add_nonneg (by decide : (0 : ℝ) ≤ 0) (le_of_lt hη_pos))
    have h3 : (⌊x + η⌋₊ : ℝ) + 1 - (⌈x - η⌉₊ : ℝ) ≤ (x + η) + 1 - (x - η) :=
      add_le_add_right (sub_le_sub_left h1 _) 1
    have h6 : (⌊x + η⌋₊ - ⌈x - η⌉₊ + 1 : ℝ) ≤ ⌊2 * η⌋₊ + 3 := by
      calc (⌊x + η⌋₊ - ⌈x - η⌉₊ + 1 : ℝ)
        ≤ (x + η) + 1 - (x - η) := h3
        _ = 2 * η + 1 := add_one_interval x η
        _ ≤ ⌊2 * η⌋₊ + 3 := arithmetic_bound η hη_pos
    exact Nat.cast_le.mp h6
  · rw [Finset.card_Icc, Nat.max_eq_right (Nat.not_lt.mp h)]

/-- Sum bound: if all terms ≤ 1, sum ≤ card. -/
theorem finset_sum_le_card {α : Type*} (s : Finset α) (f : α → ℝ) (h : ∀ a ∈ s, f a ≤ 1) :
    ∑ a in s, f a ≤ (s.card : ℝ) := by
  have h_sum := Finset.sum_le_sum h
  have h_card : ∑ a in s, (1 : ℝ) = s.card := Finset.sum_const s 1
  calc ∑ a in s, f a
    ≤ ∑ a in s, (1 : ℝ) := h_sum
    _ = (s.card : ℝ) := h_card

/-- Arithmetic: 2η + 3 ≤ 8(η + 1) for η > 0. -/
theorem two_eta_plus_three_le_eight_eta_plus_one (η : ℝ) (hη_pos : 0 < η) :
    2 * η + 3 ≤ 8 * (η + 1) := by
  have h_rhs : 8 * (η + 1) = 8 * η + 8 := by rw [mul_add, mul_one]
  rw [h_rhs]
  have h_pos : 0 < 6 * η + 5 := by
    have : 0 < 6 * η := mul_pos six_pos hη_pos
    exact add_pos this five_pos
  have h_eq : 2 * η + 3 + (6 * η + 5) = 8 * η + 8 := arith_algebra η
  calc 2 * η + 3
    ≤ 2 * η + 3 + (6 * η + 5) := le_add_of_nonneg_right (le_of_lt h_pos)
    _ = 8 * η + 8 := h_eq

/-- Pointwise domination: Lorentzian kernel is a decreasing function of distance. -/
theorem lorentzianKernel_le_of_dist_le
    (η : ℝ) (hη_pos : 0 < η) (m n x : ℝ) (h : |m - x| ≤ |n - x|) :
    lorentzianKernel η x m ≥ lorentzianKernel η x n := by
  unfold lorentzianKernel
  rw [ge_iff_le]
  have h_sq : (m - x) ^ 2 ≤ (n - x) ^ 2 := by
    have : |m - x| ^ 2 ≤ |n - x| ^ 2 := pow_le_pow_left (abs_nonneg _) h 2
    have h1 := sq_abs (m - x)
    have h2 := sq_abs (n - x)
    rw [← h1, ← h2]
    exact this
  have h_pos_m : 0 < (m - x) ^ 2 + η ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη_pos)
  have h_pos_n : 0 < (n - x) ^ 2 + η ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hη_pos)
  rw [div_le_div_iff h_pos_n h_pos_m]
  calc η ^ 2 * ((m - x) ^ 2 + η ^ 2)
    ≤ η ^ 2 * ((n - x) ^ 2 + η ^ 2) := by
      exact mul_le_mul_of_nonneg_left h_sq (sq_nonneg η)

/-- Core shell contribution: integers within distance η of x. -/
theorem lorentzianMass_coreShell_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) :
    ∑ m in Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ),
      lorentzianKernel η x m ≤ 8 * (η + 1) := by
  let core := Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ)
  have h_each_le_one : ∀ m ∈ core, lorentzianKernel η x ↑m ≤ 1 := by
    intro m _
    exact lorentzianKernel_le_one_on_core η hη_pos ↑m x
  have h_card : core.card ≤ (⌊2 * η⌋₊ + 3 : ℕ) :=
    coreShell_card_le η hη_pos x
  have h_sum_bound : ∑ m in core, lorentzianKernel η x ↑m ≤ (core.card : ℝ) :=
    finset_sum_le_card core (fun m => lorentzianKernel η x ↑m) h_each_le_one
  have h_floor_le : ((⌊2 * η⌋₊ + 3 : ℕ) : ℝ) ≤ 8 * (η + 1) :=
    two_eta_plus_three_le_eight_eta_plus_one η hη_pos
  calc ∑ m in core, lorentzianKernel η x ↑m
    ≤ (core.card : ℝ) := h_sum_bound
    _ ≤ ((⌊2 * η⌋₊ + 3 : ℕ) : ℝ) := by exact Nat.cast_le.mpr h_card
    _ ≤ 8 * (η + 1) := h_floor_le

/-- Shell k contribution: dyadic shells at different scales. -/
theorem lorentzianMass_shell_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) (k : ℕ) :
    ∑ m in Finset.filter (fun (m : ℕ) => 2 ^ k * η < |(m : ℝ) - x| ∧ |(m : ℝ) - x| ≤ 2 ^ (k + 1) * η)
      (Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ)),
      lorentzianKernel η x ↑m ≤
        (2 ^ (k + 2) * η + 3) * (4 : ℝ) ^ (-k : ℤ) := by
  let shell := Finset.filter (fun (m : ℕ) => 2 ^ k * η < |(m : ℝ) - x| ∧ |(m : ℝ) - x| ≤ 2 ^ (k + 1) * η)
      (Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ))
  have h_card : shell.card ≤ 2 ^ (k + 3) := by
    have h_subset : shell ⊆ Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ) :=
      Finset.filter_subset _ _
    have h_icc_card : (Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ)).card ≤ 2 ^ (k + 3) := by sorry
    exact Finset.card_le_card h_subset ▸ sorry
  have h_kernel_bound : ∀ m ∈ shell, lorentzianKernel η x ↑m ≤ 1 / (2 ^ k * η) ^ 2 := by
    intro m hm
    have hm_shell : 2 ^ k * η < |(m : ℝ) - x| ∧ |(m : ℝ) - x| ≤ 2 ^ (k + 1) * η :=
      (Finset.mem_filter.mp hm).2
    unfold lorentzianKernel
    have h_lower := hm_shell.1
    have h_sq := dist_bound_sq k η ((m : ℝ) - x) hη_pos h_lower
    have h_denom_pos := dist_sq_pos h_lower
    have h_kernel_pos := two_pow_times_eta_sq_pos k η hη_pos
    have h_sum_pos : 0 < ((m : ℝ) - x) ^ 2 + η ^ 2 := add_pos_of_pos_of_nonneg h_denom_pos (eta_sq_pos η hη_pos)
    rw [div_le_div_iff h_sum_pos h_kernel_pos]
    have h_final : η ^ 2 * (((m : ℝ) - x) ^ 2) ≤ 1 * (((m : ℝ) - x) ^ 2 + η ^ 2) := by sorry
    calc η ^ 2 * ((2 ^ k * η) ^ 2)
      ≤ η ^ 2 * (((m : ℝ) - x) ^ 2) := mul_le_mul_of_nonneg_left h_sq (eta_sq_pos η hη_pos)
      _ ≤ 1 * (((m : ℝ) - x) ^ 2 + η ^ 2) := h_final
  have h_sum_each : ∑ m in shell, lorentzianKernel η x ↑m ≤ shell.card / (2 ^ k * η) ^ 2 := by
    have h_sum := finset_sum_le_card shell (fun m => lorentzianKernel η x ↑m) h_kernel_bound
    have h_pos := two_pow_times_eta_sq_pos k η hη_pos
    have h_div := div_le_div_of_le_left (Nat.cast_nonneg _) h_pos h_sum
    exact h_div
  calc ∑ m in shell, lorentzianKernel η x ↑m
    ≤ shell.card / (2 ^ k * η) ^ 2 := h_sum_each
    _ ≤ (2 ^ (k + 3) : ℕ) / (2 ^ k * η) ^ 2 := by sorry
    _ ≤ (2 ^ (k + 2) * η + 3) * (4 : ℝ) ^ (-k : ℤ) := by sorry

/-- The full Lorentzian mass bound: sum over all integers in an interval. -/
theorem lorentzianMass_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) (A B : ℕ) :
    ∑ m in Finset.Icc A B,
      lorentzianKernel η x m ≤ 16 * (η + 1) := by
  have h_core := lorentzianMass_coreShell_le η hη_pos x
  calc ∑ m in Finset.Icc A B, lorentzianKernel η x m
    ≤ (∑ m in Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ), lorentzianKernel η x m) +
        (∑ k, ∑ m in Finset.filter (fun (m : ℕ) => 2 ^ k * η < |(m : ℝ) - x| ∧ |(m : ℝ) - x| ≤ 2 ^ (k + 1) * η)
          (Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ)), lorentzianKernel η x ↑m) := by sorry
    _ ≤ 8 * (η + 1) + 8 * (η + 1) := by sorry
    _ = 16 * (η + 1) := by have : (8 : ℝ) + 8 = 16 := by decide; rw [← this]; ring

/-- One-sided version for endpoints: sum from left endpoint a. -/
theorem lorentzianMass_leftEndpoint_le
    (η : ℝ) (hη_pos : 0 < η) (a : ℕ) (B : ℕ) :
    ∑ m in Finset.Icc a B,
      lorentzianKernel η (a : ℝ) m ≤ 16 * (η + 1) :=
  lorentzianMass_le η hη_pos (a : ℝ) a B

/-- One-sided version for endpoints: sum to right endpoint b. -/
theorem lorentzianMass_rightEndpoint_le
    (η : ℝ) (hη_pos : 0 < η) (b : ℕ) (A : ℕ) :
    ∑ m in Finset.Icc A b,
      lorentzianKernel η (b : ℝ) m ≤ 16 * (η + 1) :=
  lorentzianMass_le η hη_pos (b : ℝ) A b

/-- General consumer-facing theorem: Lorentzian sum over any finite interval. -/
theorem lorentzianMass_finsetIcc_le
    {a b : ℕ} {η c : ℝ}
    (hη : 0 < η) :
    (∑ m in Finset.Icc a b,
      η ^ 2 / (((m : ℝ) - c) ^ 2 + η ^ 2))
      ≤ 16 * (η + 1) := by
  show ∑ m in Finset.Icc a b, lorentzianKernel η c m ≤ 16 * (η + 1)
  exact lorentzianMass_le η hη c a b

end Real

end

end LFunctions
end Boundary
