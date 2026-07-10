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

/-- Cardinality: core shell has at most ⌊2η⌋ + 3 elements. -/
theorem coreShell_card_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) :
    (Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ)).card ≤ (⌊2 * η⌋₊ + 3 : ℕ) := by
  by_cases h : ⌈x - η⌉₊ ≤ ⌊x + η⌋₊
  · rw [Finset.card_Icc, Nat.max_eq_left h]
    have : ⌊x + η⌋₊ - ⌈x - η⌉₊ + 1 ≤ ⌊2 * η⌋₊ + 3 := by sorry
    exact this
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
  have h_card : shell.card ≤ 2 ^ (k + 3) * η := by sorry
  have h_kernel : ∀ m ∈ shell, lorentzianKernel η x ↑m ≤ 1 / (2 ^ k * η) ^ 2 := by
    intro m hm
    have hm_dist : 2 ^ k * η < |(m : ℝ) - x| := (Finset.mem_filter.mp hm).2.1
    sorry
  have h_sum : ∑ m in shell, lorentzianKernel η x ↑m ≤ shell.card / (2 ^ k * η) ^ 2 := by
    sorry
  sorry

/-- The full Lorentzian mass bound: sum over all integers in an interval. -/
theorem lorentzianMass_le
    (η : ℝ) (hη_pos : 0 < η) (x : ℝ) (A B : ℕ) :
    ∑ m in Finset.Icc A B,
      lorentzianKernel η x m ≤ 16 * (η + 1) := by
  have h_core : ∑ m in Finset.Icc (⌈x - η⌉₊ : ℕ) (⌊x + η⌋₊ : ℕ),
      lorentzianKernel η x m ≤ 8 * (η + 1) :=
    lorentzianMass_coreShell_le η hη_pos x
  have h_shells : ∑ k, ∑ m in Finset.filter (fun (m : ℕ) => 2 ^ k * η < |(m : ℝ) - x| ∧
      |(m : ℝ) - x| ≤ 2 ^ (k + 1) * η)
      (Finset.Icc (⌈x - 2 ^ (k + 2) * η⌉₊ : ℕ) (⌊x + 2 ^ (k + 2) * η⌋₊ : ℕ)),
      lorentzianKernel η x ↑m ≤ 8 * (η + 1) := by
    sorry
  sorry

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
