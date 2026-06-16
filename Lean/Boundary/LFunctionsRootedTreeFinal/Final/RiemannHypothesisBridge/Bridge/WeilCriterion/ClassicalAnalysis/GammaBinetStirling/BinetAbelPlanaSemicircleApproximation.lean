import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseGeometry

/-!
# Semicircle graph approximation for finite-height Abel-Plana collars

This file owns the graph and angle parametrizations of the right semicircle,
the staircase-to-arc convergence theorem, and the resulting right-half-core
Cauchy-Goursat wrapper consumed by finite-hole boundary accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology


/-- Right semicircle graph point at vertical coordinate `y`. -/
noncomputable def Complex.rightSemicircleGraphPoint
    (c : ℂ)
    (ρ y : ℝ) : ℂ :=
  (((c.re + Complex.rightSemicircleGraphRe ρ y : ℝ) : ℂ) +
    Complex.I * (((c.im + y : ℝ) : ℂ)))

/-- Real coordinate of the right-semicircle graph point. -/
theorem Complex.rightSemicircleGraphPoint_re
    (c : ℂ)
    (ρ y : ℝ) :
    (Complex.rightSemicircleGraphPoint c ρ y).re =
      c.re + Complex.rightSemicircleGraphRe ρ y := by
  dsimp [Complex.rightSemicircleGraphPoint]
  simp

/-- Imaginary coordinate of the right-semicircle graph point. -/
theorem Complex.rightSemicircleGraphPoint_im
    (c : ℂ)
    (ρ y : ℝ) :
    (Complex.rightSemicircleGraphPoint c ρ y).im = c.im + y := by
  dsimp [Complex.rightSemicircleGraphPoint]
  simp

/-- The graph real coordinate belongs to the radial interval over the closed
height interval. -/
theorem Complex.rightSemicircleGraphRe_mem_radius_uIcc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {y : ℝ}
    (hy : y ∈ Set.Icc (-ρ) ρ) :
    Complex.rightSemicircleGraphRe ρ y ∈ [[(0 : ℝ), ρ]] := by
  have hy_uIcc : y ∈ [[-ρ, ρ]] := by
    have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
      Set.uIcc_of_le (Complex.neg_radius_le_radius hρ)
    exact huIcc.symm ▸ hy
  exact Complex.rightSemicircleGraphRe_mem_radius_uIcc_of_height_mem hρ hy_uIcc

/-- A point of the closed height interval also belongs to the unordered
semicircle height interval. -/
theorem Complex.mem_semicircle_height_uIcc_of_mem_Icc
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy : y ∈ Set.Icc (-ρ) ρ) :
    y ∈ [[-ρ, ρ]] := by
  have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
    Set.uIcc_of_le (Complex.neg_radius_le_radius hρ)
  exact huIcc.symm ▸ hy

/-- A point with the same height as a graph point is separated from it by the
real-coordinate error. -/
theorem Complex.dist_realLinePoint_rightSemicircleGraphPoint
    (c : ℂ)
    (ρ x y : ℝ) :
    dist
      ((((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ y) =
    |x - Complex.rightSemicircleGraphRe ρ y| := by
  let z₁ : ℂ :=
    (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ)))
  let z₂ : ℂ := Complex.rightSemicircleGraphPoint c ρ y
  have him : z₁.im = z₂.im := by
    dsimp [z₁, z₂]
    rw [Complex.rightSemicircleGraphPoint_im]
  have hdist : dist z₁ z₂ = dist z₁.re z₂.re :=
    Complex.dist_of_im_eq him
  have hz₁_re : z₁.re = c.re + x := by
    dsimp [z₁]
    simp
  have hz₂_re : z₂.re = c.re + Complex.rightSemicircleGraphRe ρ y := by
    dsimp [z₂]
    exact Complex.rightSemicircleGraphPoint_re c ρ y
  calc
    dist
      ((((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ y)
        = dist z₁ z₂ := rfl
    _ = dist z₁.re z₂.re := hdist
    _ = |x - Complex.rightSemicircleGraphRe ρ y| := by
      rw [hz₁_re, hz₂_re]
      simp [Real.dist_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

/-- Vertical part of the right-semicircle graph line integral. -/
noncomputable def Complex.rightSemicircleGraphVerticalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  Complex.I *
    ∫ y : ℝ in (-ρ)..ρ,
      f (Complex.rightSemicircleGraphPoint c ρ y)

/-- Angle-parametrized right-semicircle line integral. -/
noncomputable def Complex.rightSemicircleAngleIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Horizontal part of the right-semicircle graph line integral.

This is the nonvertical contribution left after subtracting the `I dy` part
from the angle-parametrized line integral.  It is not zero: it is the `dx`
piece of the circular graph path. -/
noncomputable def Complex.rightSemicircleGraphHorizontalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ) : ℂ :=
  Complex.rightSemicircleAngleIntegral f c ρ -
    Complex.rightSemicircleGraphVerticalIntegral f c ρ

/-- The right circular graph is continuous on the closed height interval. -/
theorem Complex.continuousOn_rightSemicircleGraphRe_Icc
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ContinuousOn
      (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
      (Set.Icc (-ρ) ρ) := by
  have hnonneg :
      ∀ y ∈ Set.Icc (-ρ) ρ, 0 ≤ ρ ^ 2 - y ^ 2 := by
    intro y hy
    have hy_abs : |y| ≤ ρ := abs_le.mpr hy
    have hy_sq : y ^ 2 ≤ ρ ^ 2 := sq_le_sq.mpr hy_abs
    exact sub_nonneg.mpr hy_sq
  have hinner :
      ContinuousOn (fun y : ℝ => ρ ^ 2 - y ^ 2) (Set.Icc (-ρ) ρ) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  dsimp [Complex.rightSemicircleGraphRe]
  exact Real.continuousOn_sqrt.comp hinner hnonneg

/-- The right-semicircle graph parametrization is continuous on the closed
height interval. -/
theorem Complex.continuousOn_rightSemicircleGraphPoint_Icc
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ContinuousOn
      (fun y : ℝ => Complex.rightSemicircleGraphPoint c ρ y)
      (Set.Icc (-ρ) ρ) := by
  have hgraph_cont :
      ContinuousOn
        (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphRe_Icc hρ
  dsimp [Complex.rightSemicircleGraphPoint]
  exact
    ((continuous_const.add (Complex.continuous_ofReal.comp_continuousOn hgraph_cont)).add
      (continuous_const.mul
        (continuous_const.add continuous_ofReal).continuousOn))

/-- The graph point lies on the deleted right-half-collar boundary. -/
theorem Complex.rightSemicircleGraphPoint_mem_core_self
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {y : ℝ}
    (hy : y ∈ Set.Icc (-ρ) ρ) :
    Complex.rightSemicircleGraphPoint c ρ y ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hx_bounds :
      Complex.rightSemicircleGraphRe ρ y ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleGraphRe_mem_radius_uIcc hρ.le hy
  have hy_bounds : y ∈ [[-ρ, ρ]] :=
    Complex.mem_semicircle_height_uIcc_of_mem_Icc hρ.le hy
  have hgraph :
      Complex.rightSemicircleGraphRe ρ y ≤ Complex.rightSemicircleGraphRe ρ y :=
    le_rfl
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- The graph-parametrized vertical integrand is continuous on the height
interval. -/
theorem Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    ContinuousOn
      (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
      (Set.Icc (-ρ) ρ) := by
  have hparam :
      ContinuousOn
        (fun y : ℝ => Complex.rightSemicircleGraphPoint c ρ y)
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphPoint_Icc c hρ
  have hmaps :
      MapsTo
        (fun y : ℝ => Complex.rightSemicircleGraphPoint c ρ y)
        (Set.Icc (-ρ) ρ)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
  exact hcont.comp_continuousOn hparam hmaps

/-- The graph-parametrized probe is bounded on the closed height interval. -/
theorem Complex.exists_bound_rightSemicircleGraphProbe_norm
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ y ∈ Set.Icc (-ρ) ρ,
        ‖f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ B := by
  have hprobe_cont :
      ContinuousOn
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
      f c hρ hcont
  have hcompact : IsCompact (Set.Icc (-ρ) ρ) := isCompact_Icc
  have hbounded :
      Bornology.IsBounded
        ((fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y)) ''
          Set.Icc (-ρ) ρ) :=
    (hcompact.image_of_continuousOn hprobe_cont).isBounded
  rcases Metric.isBounded_iff_subset_closedBall 0.mp hbounded with ⟨B₀, hB₀⟩
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  refine ⟨B, hB_nonneg, ?_⟩
  intro y hy
  have hmem :
      f (Complex.rightSemicircleGraphPoint c ρ y) ∈
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y)) ''
          Set.Icc (-ρ) ρ := ⟨y, hy, rfl⟩
  have hball := hB₀ hmem
  have hnorm_le_B₀ :
      ‖f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ B₀ := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hball
  exact le_trans hnorm_le_B₀ (le_max_left B₀ 0)

/-- The graph-parametrized vertical integrand is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleGraphVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
      volume
      (-ρ)
      ρ := by
  exact
    (Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
      f c hρ hcont).intervalIntegrable

/-- The graph vertical integral splits over the staircase height partition. -/
theorem Complex.rightSemicircleGraphVerticalIntegral_eq_sum_cells
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ) :
    Complex.rightSemicircleGraphVerticalIntegral f c ρ =
      Complex.I *
        ∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (Complex.rightSemicircleGraphPoint c ρ y) := by
  let F : ℝ → ℂ := fun y => f (Complex.rightSemicircleGraphPoint c ρ y)
  let a : ℕ → ℝ := fun k => Complex.rightSemicircleStaircaseY ρ m k
  have hA : a 0 = -ρ := by
    dsimp [a]
    exact Complex.rightSemicircleStaircaseY_zero ρ m
  have hB : a (m + 1) = ρ := by
    dsimp [a]
    exact Complex.rightSemicircleStaircaseY_last ρ m
  have hF :
      IntervalIntegrable F volume (-ρ) ρ :=
    Complex.intervalIntegrable_rightSemicircleGraphVertical f c hρ hcont
  have hint :
      ∀ k < m + 1, IntervalIntegrable F volume (a k) (a (k + 1)) := by
    intro k hk
    have hk_cell : k ∈ Finset.range (m + 1) :=
      Finset.mem_range.mpr hk
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk_cell
    have hk1 : k + 1 ∈ Finset.range (m + 2) := by
      exact Complex.staircase_upper_sample_mem_range hk_cell
    have hyk :
        a k ∈ [[-ρ, ρ]] := by
      dsimp [a]
      exact Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
    have hyk1 :
        a (k + 1) ∈ [[-ρ, ρ]] := by
      dsimp [a]
      exact Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
    exact Complex.intervalIntegrable_of_mem_uIcc hF hyk hyk1
  dsimp [Complex.rightSemicircleGraphVerticalIntegral, F, a]
  rw [Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
    (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
    (fun k : ℕ => Complex.rightSemicircleStaircaseY ρ m k)
    (m + 1) (-ρ) ρ hA hB hint]

/-- The staircase vertical sum is `I` times the sum of its real-parameterized
cell integrals. -/
theorem Complex.sum_rightSemicircleStaircaseVerticalIntegral_eq_I_mul_sum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) =
      Complex.I *
        ∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))) := by
  dsimp [Complex.rightSemicircleStaircaseVerticalIntegral]
  rw [Finset.mul_sum]

/-- The uniform height mesh of the staircase partition. -/
theorem Complex.rightSemicircleStaircase_cell_length
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k =
        (2 * ρ) / (m + 1 : ℝ) := by
  exact Complex.rightSemicircleStaircaseY_succ_sub ρ m k

/-- The real number `2` is nonnegative. -/
theorem real_two_nonneg :
    0 ≤ (2 : ℝ) := by
  exact zero_le_two

/-- A successor natural number has positive real cast. -/
theorem real_nat_succ_cast_pos
    (m : ℕ) :
    0 < (m + 1 : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.succ_pos m)

/-- A successor natural number has nonzero real cast. -/
theorem real_nat_succ_cast_ne_zero
    (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) ≠ 0 := by
  exact ne_of_gt (real_nat_succ_cast_pos m)

/-- The real number `6` is positive. -/
theorem real_six_pos : 0 < (6 : ℝ) := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 5)

/-- Half of `π` is nonnegative. -/
theorem real_pi_div_two_nonneg : 0 ≤ Real.pi / 2 := by
  exact div_nonneg (le_of_lt Real.pi_pos) zero_le_two

/-- Twice a positive radius is positive. -/
theorem real_two_mul_pos_of_pos
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    0 < 2 * ρ := by
  exact mul_pos zero_lt_two hρ

/-- Six times a positive radius is positive. -/
theorem real_six_mul_pos_of_pos
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    0 < 6 * ρ := by
  exact mul_pos real_six_pos hρ

/-- Absolute length of one uniform staircase height cell. -/
theorem Complex.rightSemicircleStaircase_cell_length_abs
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k| =
        (2 * ρ) / (m + 1 : ℝ) := by
  rw [Complex.rightSemicircleStaircase_cell_length]
  have hden_nonneg : 0 ≤ (m + 1 : ℝ) := by
    exact le_of_lt (real_nat_succ_cast_pos m)
  exact abs_of_nonneg
    (div_nonneg (mul_nonneg real_two_nonneg hρ) hden_nonneg)

/-- A real number below `N` is below `m+1` whenever `N ≤ m`. -/
theorem real_lt_nat_succ_of_lt_nat_of_nat_le
    {q : ℝ}
    {N m : ℕ}
    (hN : q < (N : ℝ))
    (hm : N ≤ m) :
    q < (m + 1 : ℝ) := by
  have hN_le_m : (N : ℝ) ≤ (m : ℝ) := by
    exact Nat.cast_le.mpr hm
  have hm_lt_succ : (m : ℝ) < (m + 1 : ℝ) := by
    exact Nat.cast_lt.mpr (Nat.lt_succ_self m)
  exact lt_of_lt_of_le hN (le_of_lt (lt_of_le_of_lt hN_le_m hm_lt_succ))

/-- Dividing a strict product bound by a positive successor denominator. -/
theorem div_nat_succ_lt_of_lt_mul
    {A δ : ℝ}
    (hδ : 0 < δ)
    (m : ℕ)
    (hA : A < δ * (m + 1 : ℝ)) :
    A / (m + 1 : ℝ) < δ := by
  have hden : 0 < (m + 1 : ℝ) :=
    real_nat_succ_cast_pos m
  rw [div_lt_iff₀' hden]
  exact hA

/-- Dividing by a positive scale and multiplying back by that scale recovers
the original quantity. -/
theorem div_mul_cancel_of_pos_right
    {ε A : ℝ}
    (hA : 0 < A) :
    (ε / A) * A = ε := by
  have hA_ne : A ≠ 0 := ne_of_gt hA
  exact div_mul_cancel₀ ε hA_ne

/-- Three error contributions of size `η * (2ρ)` are bounded by the single
scale `η * (6ρ)`. -/
theorem three_two_radius_errors_le_six_radius_error
    {η ρ : ℝ}
    (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) :
    η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) ≤ η * (6 * ρ) := by
  have hsum :
      (2 * ρ + 2 * ρ) + 2 * ρ = 6 * ρ := by
    calc
      (2 * ρ + 2 * ρ) + 2 * ρ
          = (2 + 2 : ℝ) * ρ + 2 * ρ := by
            rw [add_mul]
      _ = ((2 + 2 : ℝ) + 2) * ρ := by
            rw [add_mul]
      _ = 6 * ρ := rfl
  have heq :
      η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) =
        η * (6 * ρ) := by
    calc
      η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ)
          = η * (2 * ρ + 2 * ρ) + η * (2 * ρ) := by
            rw [mul_add]
      _ = η * ((2 * ρ + 2 * ρ) + 2 * ρ) := by
            rw [mul_add]
      _ = η * (6 * ρ) := by
            rw [hsum]
  exact le_of_eq heq

/-- Two quantities each bounded by the same radius have sum bounded by twice
that radius. -/
theorem add_le_two_mul_of_each_le
    {a b ρ : ℝ}
    (ha : a ≤ ρ)
    (hb : b ≤ ρ) :
    a + b ≤ 2 * ρ := by
  calc
    a + b ≤ ρ + ρ := add_le_add ha hb
    _ = 2 * ρ := (two_mul ρ).symm

/-- The uniform staircase mesh tends to zero. -/
theorem Complex.eventually_rightSemicircleStaircase_cell_length_lt
    {ρ δ : ℝ}
    (hρ : 0 < ρ)
    (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k ∈ Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k| < δ := by
  rcases exists_nat_gt ((2 * ρ) / δ) with ⟨N, hN⟩
  filter_upwards [eventually_ge_atTop N] with m hm k hk
  have hquot_lt_succ : (2 * ρ) / δ < (m + 1 : ℝ) := by
    exact real_lt_nat_succ_of_lt_nat_of_nat_le hN hm
  have hmul_lt : 2 * ρ < δ * (m + 1 : ℝ) := by
    exact (div_lt_iff₀ hδ).mp hquot_lt_succ
  have hlen_lt : (2 * ρ) / (m + 1 : ℝ) < δ := by
    exact div_nat_succ_lt_of_lt_mul hδ m hmul_lt
  rw [Complex.rightSemicircleStaircase_cell_length_abs hρ.le]
  exact hlen_lt

/-- A uniform partition with `m + 1` cells of length `2ρ / (m + 1)` has total
length `2ρ`. -/
theorem nat_succ_mul_uniform_semicircle_cell_length
    (ρ : ℝ)
    (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) * ((2 * ρ) / ((m + 1 : ℕ) : ℝ)) = 2 * ρ := by
  have hden : ((m + 1 : ℕ) : ℝ) ≠ 0 :=
    real_nat_succ_cast_ne_zero m
  exact mul_div_cancel₀ (2 * ρ) hden

/-- Total length of the uniform staircase height partition. -/
theorem Complex.sum_rightSemicircleStaircase_cell_lengths
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
        Complex.rightSemicircleStaircaseY ρ m k|) = 2 * ρ := by
  simp_rw [Complex.rightSemicircleStaircase_cell_length_abs hρ]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact nat_succ_mul_uniform_semicircle_cell_length ρ m

/-- Finite-difference sample sum for the horizontal staircase contribution. -/
noncomputable def Complex.rightSemicircleStaircaseHorizontalSampleSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∑ k in Finset.range (m + 1),
    f (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)) *
      (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))) +
    f (Complex.rightSemicircleGraphPoint c ρ ρ) *
      (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))

/-- Graph-coordinate finite-difference sample sum for the horizontal
component of the right semicircle.  This is the canonical Riemann-Stieltjes
sample before replacing the graph finite differences by the exterior safe
staircase finite differences. -/
noncomputable def Complex.rightSemicircleGraphHorizontalSampleSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∑ k in Finset.range (m + 1),
    f (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)) *
      (((Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))

/-- Angle coordinate attached to the uniform height grid on the right
semicircle. -/
noncomputable def Complex.rightSemicircleAngleGrid
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ)

/-- The bottom height-grid point has normalized height `-1`. -/
theorem Complex.rightSemicircleAngleGrid_bottom_ratio
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m 0 / ρ = -1 := by
  rw [Complex.rightSemicircleStaircaseY_zero]
  exact neg_div_self (ne_of_gt hρ)

/-- The angle grid starts at `-π/2`. -/
theorem Complex.rightSemicircleAngleGrid_zero
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleAngleGrid ρ m 0 = -(Real.pi / 2) := by
  dsimp [Complex.rightSemicircleAngleGrid]
  rw [Complex.rightSemicircleAngleGrid_bottom_ratio hρ m, Real.arcsin_neg_one]

/-- The top height-grid point has normalized height `1`. -/
theorem Complex.rightSemicircleAngleGrid_top_ratio
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (m + 1) / ρ = 1 := by
  rw [Complex.rightSemicircleStaircaseY_last]
  exact div_self (ne_of_gt hρ)

/-- The angle grid ends at `π/2`. -/
theorem Complex.rightSemicircleAngleGrid_last
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleAngleGrid ρ m (m + 1) = Real.pi / 2 := by
  dsimp [Complex.rightSemicircleAngleGrid]
  rw [Complex.rightSemicircleAngleGrid_top_ratio hρ m, Real.arcsin_one]

/-- Every angle-grid point lies in the right-semicircle angle interval. -/
theorem Complex.rightSemicircleAngleGrid_mem_Icc
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleAngleGrid ρ m k ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  dsimp [Complex.rightSemicircleAngleGrid]
  exact Real.arcsin_mem_Icc _

/-- Dividing a height in `[-ρ,ρ]` by a positive radius lands in `[-1,1]`. -/
theorem div_radius_mem_unit_Icc_of_height_mem
    {ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-ρ, ρ]]) :
    -1 ≤ y / ρ ∧ y / ρ ≤ 1 := by
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
      Set.uIcc_of_le (Complex.neg_radius_le_radius hρ.le)
    exact huIcc ▸ hy
  have hleft : -1 ≤ y / ρ := by
    rw [neg_le_div_iff₀ hρ]
    exact hy_bounds.1
  have hright : y / ρ ≤ 1 := by
    rw [div_le_one hρ]
    exact hy_bounds.2
  exact And.intro hleft hright

/-- The sine of the angle-grid point recovers the height grid point. -/
theorem Complex.rightSemicircleAngleGrid_sin
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    ρ * Real.sin (Complex.rightSemicircleAngleGrid ρ m k) =
      Complex.rightSemicircleStaircaseY ρ m k := by
  have hy :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk
  have hdiv_bounds :
      -1 ≤ Complex.rightSemicircleStaircaseY ρ m k / ρ ∧
        Complex.rightSemicircleStaircaseY ρ m k / ρ ≤ 1 :=
    div_radius_mem_unit_Icc_of_height_mem hρ hy
  dsimp [Complex.rightSemicircleAngleGrid]
  rw [Real.sin_arcsin hdiv_bounds.1 hdiv_bounds.2]
  exact mul_div_cancel₀ (Complex.rightSemicircleStaircaseY ρ m k)
    (ne_of_gt hρ)

/-- The right-semicircle angle unordered interval is the usual ordered closed
interval. -/
theorem rightSemicircleAngle_uIcc_eq_Icc :
    [[-(Real.pi / 2), Real.pi / 2]] =
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hleft : -(Real.pi / 2) ≤ Real.pi / 2 := by
    have hhalf_nonneg : 0 ≤ Real.pi / 2 :=
      real_pi_div_two_nonneg
    exact neg_le_self hhalf_nonneg
  exact Set.uIcc_of_le hleft

/-- Membership in the right-semicircle angle unordered interval gives
membership in the ordered interval. -/
theorem mem_rightSemicircleAngle_Icc_of_mem_uIcc
    {θ : ℝ}
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  exact rightSemicircleAngle_uIcc_eq_Icc ▸ hθ

/-- Multiplying a sine value by a nonnegative radius keeps it in the vertical
height interval of that radius. -/
theorem radius_mul_sin_mem_height_Icc
    {ρ θ : ℝ}
    (hρ : 0 ≤ ρ) :
    ρ * Real.sin θ ∈ Set.Icc (-ρ) ρ := by
  have hsin_lower : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
  have hsin_upper : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have hleft : -ρ ≤ ρ * Real.sin θ := by
    calc
      -ρ = ρ * (-1 : ℝ) := (mul_neg_one ρ).symm
      _ ≤ ρ * Real.sin θ := mul_le_mul_of_nonneg_left hsin_lower hρ
  have hright : ρ * Real.sin θ ≤ ρ := by
    calc
      ρ * Real.sin θ ≤ ρ * (1 : ℝ) :=
        mul_le_mul_of_nonneg_left hsin_upper hρ
      _ = ρ := mul_one ρ
  exact And.intro hleft hright

/-- The angle grid is monotone because the height grid is monotone and
`arcsin` is monotone. -/
theorem Complex.rightSemicircleAngleGrid_monotone
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    ∀ k : ℕ, k < m + 1 →
      Complex.rightSemicircleAngleGrid ρ m k ≤
        Complex.rightSemicircleAngleGrid ρ m (k + 1) := by
  intro k hk
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ.le m k
  dsimp [Complex.rightSemicircleAngleGrid]
  exact Real.monotone_arcsin (div_le_div_of_nonneg_right hy_le hρ.le)

/-- The angle-grid cell endpoints both lie in the right-semicircle angle
interval. -/
theorem Complex.rightSemicircleAngleGrid_cell_endpoints_mem_Icc
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
      Complex.rightSemicircleAngleGrid ρ m k ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) ∧
      Complex.rightSemicircleAngleGrid ρ m (k + 1) ∈
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  exact
    ⟨Complex.rightSemicircleAngleGrid_mem_Icc hρ hk0,
      Complex.rightSemicircleAngleGrid_mem_Icc hρ hk1⟩

/-- Each angle-grid cell is contained in the right-semicircle angle interval. -/
theorem Complex.rightSemicircleAngleGrid_cell_subset_Icc
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    [[Complex.rightSemicircleAngleGrid ρ m k,
      Complex.rightSemicircleAngleGrid ρ m (k + 1)]] ⊆
        Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  intro θ hθ
  have hendpoints :=
    Complex.rightSemicircleAngleGrid_cell_endpoints_mem_Icc hρ hk
  have hcell :
      (Complex.rightSemicircleAngleGrid ρ m k ≤ θ ∧
          θ ≤ Complex.rightSemicircleAngleGrid ρ m (k + 1)) ∨
        (Complex.rightSemicircleAngleGrid ρ m (k + 1) ≤ θ ∧
          θ ≤ Complex.rightSemicircleAngleGrid ρ m k) := by
    simpa [Set.mem_uIcc] using hθ
  rcases hcell with hcell | hcell
  · exact
      ⟨le_trans hendpoints.1.1 hcell.1,
        le_trans hcell.2 hendpoints.2.2⟩
  · exact
      ⟨le_trans hendpoints.2.1 hcell.1,
        le_trans hcell.2 hendpoints.1.2⟩

/-- The angle-grid mesh tends to zero.  This is the compact-uniform-continuity
translation of the uniform height-grid mesh through `arcsin`. -/
theorem Complex.eventually_rightSemicircleAngleGrid_cell_length_lt
    {ρ δ : ℝ}
    (hρ : 0 < ρ)
    (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop,
      ∀ k ∈ Finset.range (m + 1),
        |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
          Complex.rightSemicircleAngleGrid ρ m k| < δ := by
  have harcsin_cont :
      ContinuousOn Real.arcsin (Set.Icc (-1 : ℝ) 1) :=
    continuous_arcsin.continuousOn
  have harcsin_uniform :
      UniformContinuousOn Real.arcsin (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous harcsin_cont
  rcases (Metric.uniformContinuousOn_iff.mp harcsin_uniform δ hδ) with
    ⟨η, hη, hη_modulus⟩
  let ηρ : ℝ := η * ρ
  have hηρ_pos : 0 < ηρ := mul_pos hη hρ
  have hheight :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| < ηρ :=
    Complex.eventually_rightSemicircleStaircase_cell_length_lt hρ hηρ_pos
  filter_upwards [hheight] with m hm k hk
  have hendpoints :=
    Complex.rightSemicircleAngleGrid_cell_endpoints_mem_Icc hρ hk
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
  have hx0 :
      Complex.rightSemicircleStaircaseY ρ m k / ρ ∈
        Set.Icc (-1 : ℝ) 1 := by
    exact div_radius_mem_unit_Icc_of_height_mem hρ hy0
  have hx1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ ∈
        Set.Icc (-1 : ℝ) 1 := by
    exact div_radius_mem_unit_Icc_of_height_mem hρ hy1
  have hratio :
      dist
        (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ)
        (Complex.rightSemicircleStaircaseY ρ m k / ρ) < η := by
    dsimp [dist]
    rw [← sub_div]
    have hρnorm : ‖ρ‖ = ρ := by
      exact Real.norm_of_nonneg hρ.le
    rw [norm_div, hρnorm]
    rw [div_lt_iff₀ hρ]
    exact hm k hk
  have hclose :
      dist
        (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ))
        (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ)) < δ :=
    hη_modulus
      (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ) hx1
      (Complex.rightSemicircleStaircaseY ρ m k / ρ) hx0
      hratio
  simpa [Complex.rightSemicircleAngleGrid, dist_eq_norm, Real.norm_eq_abs,
    abs_sub_comm] using hclose

/-- One cosine chord on the angle grid is exactly the integral of its
derivative over the corresponding angle cell. -/
theorem Complex.rightSemicircleAngleGrid_cos_chord_eq_integral_dx
    {ρ : ℝ}
    (m k : ℕ) :
    ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
        ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) =
      ∫ θ : ℝ in
        Complex.rightSemicircleAngleGrid ρ m k..
          Complex.rightSemicircleAngleGrid ρ m (k + 1),
        -ρ * Real.sin θ := by
  let G : ℝ → ℝ := fun θ => ρ * Real.cos θ
  let G' : ℝ → ℝ := fun θ => -ρ * Real.sin θ
  have hderiv : ∀ θ ∈ [[Complex.rightSemicircleAngleGrid ρ m k,
      Complex.rightSemicircleAngleGrid ρ m (k + 1)]],
      HasDerivAt G (G' θ) θ := by
    intro θ _hθ
    dsimp [G, G']
    have hcos := Real.hasDerivAt_cos θ
    simpa [neg_mul, mul_comm, mul_left_comm, mul_assoc] using
      hcos.const_mul ρ
  have hint :
      IntervalIntegrable G' volume
        (Complex.rightSemicircleAngleGrid ρ m k)
        (Complex.rightSemicircleAngleGrid ρ m (k + 1)) := by
    exact (continuous_const.mul continuous_sin).neg.intervalIntegrable
  have hfund :
      (∫ θ : ℝ in
        Complex.rightSemicircleAngleGrid ρ m k..
          Complex.rightSemicircleAngleGrid ρ m (k + 1),
        G' θ) =
        G (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
          G (Complex.rightSemicircleAngleGrid ρ m k) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  exact hfund.symm

/-- The right-semicircle radical simplifies to the squared cosine coordinate. -/
theorem radius_sq_sub_radius_mul_sin_sq_eq_radius_mul_cos_sq
    (ρ θ : ℝ) :
    ρ ^ 2 - (ρ * Real.sin θ) ^ 2 = (ρ * Real.cos θ) ^ 2 := by
  calc
    ρ ^ 2 - (ρ * Real.sin θ) ^ 2
        = ρ ^ 2 - ρ ^ 2 * Real.sin θ ^ 2 := by
          rw [mul_pow]
    _ = ρ ^ 2 * 1 - ρ ^ 2 * Real.sin θ ^ 2 := by
          rw [mul_one]
    _ = ρ ^ 2 * (1 - Real.sin θ ^ 2) := by
          exact (mul_sub (ρ ^ 2) 1 (Real.sin θ ^ 2)).symm
    _ = ρ ^ 2 * Real.cos θ ^ 2 := by
      rw [← Real.cos_sq]
    _ = (ρ * Real.cos θ) ^ 2 := by
      rw [mul_pow]

/-- The sine parametrization sends the lower angle endpoint to the lower
height endpoint. -/
theorem radius_mul_sin_neg_pi_div_two
    (ρ : ℝ) :
    ρ * Real.sin (-(Real.pi / 2)) = -ρ := by
  rw [Real.sin_neg, Real.sin_pi_div_two]
  exact mul_neg_one ρ

/-- The sine parametrization sends the upper angle endpoint to the upper
height endpoint. -/
theorem radius_mul_sin_pi_div_two
    (ρ : ℝ) :
    ρ * Real.sin (Real.pi / 2) = ρ := by
  rw [Real.sin_pi_div_two]
  exact mul_one ρ

/-- Multiplying the sine component of a circular tangent by `I²` gives the
negative horizontal component. -/
theorem Complex.I_real_mul_real_mul_I_eq_neg_real_mul
    (ρ s : ℝ) :
    (Complex.I * (ρ : ℂ)) * ((s : ℂ) * Complex.I) =
      ((-ρ * s : ℝ) : ℂ) := by
  calc
    (Complex.I * (ρ : ℂ)) * ((s : ℂ) * Complex.I)
        = (Complex.I * Complex.I) * ((ρ : ℂ) * (s : ℂ)) := by
      exact mul_mul_mul_comm Complex.I (ρ : ℂ) (s : ℂ) Complex.I
    _ = (-1 : ℂ) * ((ρ : ℂ) * (s : ℂ)) := by
      rw [Complex.I_mul_I]
    _ = -((ρ : ℂ) * (s : ℂ)) := neg_one_mul ((ρ : ℂ) * (s : ℂ))
    _ = -(((ρ * s : ℝ) : ℂ)) := by
      exact congrArg Neg.neg (Complex.ofReal_mul ρ s).symm
    _ = ((-(ρ * s) : ℝ) : ℂ) := by
      exact (Complex.ofReal_neg (ρ * s)).symm
    _ = ((-ρ * s : ℝ) : ℂ) := by
      rw [neg_mul]

/-- The cosine component of a circular tangent is the vertical component. -/
theorem Complex.I_real_mul_real_eq_I_mul_real_mul
    (ρ c : ℝ) :
    (Complex.I * (ρ : ℂ)) * (c : ℂ) =
      Complex.I * (((ρ * c : ℝ) : ℂ)) := by
  calc
    (Complex.I * (ρ : ℂ)) * (c : ℂ)
        = Complex.I * ((ρ : ℂ) * (c : ℂ)) :=
      (mul_assoc Complex.I (ρ : ℂ) (c : ℂ)).symm
    _ = Complex.I * (((ρ * c : ℝ) : ℂ)) := by
      exact congrArg (fun z => Complex.I * z) (Complex.ofReal_mul ρ c).symm

/-- The raw tangent vector of the angle-parametrized right semicircle. -/
theorem rightSemicircleAngle_tangentVector_decompose
    (ρ θ : ℝ) :
    Complex.I * (ρ : ℂ) *
        Complex.exp (Complex.I * (θ : ℂ)) =
      (((-ρ * Real.sin θ : ℝ) : ℂ)) +
        Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)) := by
  calc
    Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
        =
      Complex.I * (ρ : ℂ) *
        (((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.exp_mul_I]
    _ =
      (Complex.I * (ρ : ℂ)) * ((Real.cos θ : ℝ) : ℂ) +
        (Complex.I * (ρ : ℂ)) * (((Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      exact mul_add (Complex.I * (ρ : ℂ)) ((Real.cos θ : ℝ) : ℂ)
        (((Real.sin θ : ℝ) : ℂ) * Complex.I)
    _ =
      Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)) +
        (((-ρ * Real.sin θ : ℝ) : ℂ)) := by
      rw [Complex.I_real_mul_real_eq_I_mul_real_mul]
      rw [Complex.I_real_mul_real_mul_I_eq_neg_real_mul]
    _ =
      (((-ρ * Real.sin θ : ℝ) : ℂ)) +
        Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)) := by
      exact add_comm
        (Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)))
        (((-ρ * Real.sin θ : ℝ) : ℂ))

/-- A scalar factor may be moved across the vertical `I` component. -/
theorem Complex.mul_I_vertical_component_comm
    (A B : ℂ) :
    A * (Complex.I * B) =
      Complex.I * (A * B) := by
  calc
    A * (Complex.I * B) = (A * Complex.I) * B := mul_assoc A Complex.I B
    _ = (Complex.I * A) * B := by
      rw [mul_comm A Complex.I]
    _ = Complex.I * (A * B) := (mul_assoc Complex.I A B).symm

/-- The complex tangent vector on the angle-parametrized right semicircle
splits into its horizontal and vertical differential components. -/
theorem rightSemicircleAngle_tangentFactor_decompose
    (A : ℂ)
    (ρ θ : ℝ) :
    A * (Complex.I * (ρ : ℂ) *
        Complex.exp (Complex.I * (θ : ℂ))) =
      A * (((-ρ * Real.sin θ : ℝ) : ℂ)) +
        Complex.I * (A * ((ρ * Real.cos θ : ℝ) : ℂ)) := by
  calc
    A * (Complex.I * (ρ : ℂ) *
        Complex.exp (Complex.I * (θ : ℂ)))
        =
      A * (((( -ρ * Real.sin θ : ℝ) : ℂ)) +
        Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ))) := by
      exact congrArg (fun z => A * z)
        (rightSemicircleAngle_tangentVector_decompose ρ θ)
    _ =
      A * (((-ρ * Real.sin θ : ℝ) : ℂ)) +
        A * (Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ))) := by
      exact mul_add A (((-ρ * Real.sin θ : ℝ) : ℂ))
        (Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)))
    _ =
      A * (((-ρ * Real.sin θ : ℝ) : ℂ)) +
        Complex.I * (A * ((ρ * Real.cos θ : ℝ) : ℂ)) := by
      exact congrArg
        (fun z => A * (((-ρ * Real.sin θ : ℝ) : ℂ)) + z)
        (Complex.mul_I_vertical_component_comm A (((ρ * Real.cos θ : ℝ) : ℂ)))

/-- Subtracting the vertical component from a sum of horizontal and vertical
components recovers the horizontal component. -/
theorem horizontal_component_eq_of_sum_eq_add_vertical
    {H V S : ℂ}
    (hS : S = H + V) :
    S - V = H := by
  calc
    S - V = (H + V) - V := by rw [hS]
    _ = H := add_sub_cancel_right H V

/-- Re-inserting the subtracted summand recovers the original summand. -/
theorem add_sub_right_cancel'
    (A B : ℂ) :
    A + (B - A) = B := by
  calc
    A + (B - A) = (B - A) + A := add_comm A (B - A)
    _ = B := sub_add_cancel B A

/-- A subtracted vertical component reassembles with the vertical component. -/
theorem horizontal_add_vertical_eq_total
    (A V : ℂ) :
    (A - V) + V = A :=
  sub_add_cancel A V

/-- Splitting a horizontal-plus-top sample error into its horizontal and top
parts. -/
theorem horizontal_top_sample_error_decompose
    (H T S Stop : ℂ) :
    (H + T) - (S + Stop) = (H - S) + (T - Stop) := by
  exact add_sub_add_comm H T S Stop

/-- Inserting and then cancelling a middle term decomposes a difference. -/
theorem sub_eq_sub_add_add_sub
    (A S B : ℂ) :
    A - B = (A - S) + (S - B) := by
  calc
    A - B = ((A - S) + S) - B := by
      rw [sub_add_cancel]
    _ = (A - S) + (S - B) := by
      exact add_sub_assoc (A - S) S B

/-- Splitting the polygonal arc error into horizontal approximation,
horizontal quadrature, and vertical approximation errors. -/
theorem polygonal_arc_error_decompose_additive
    (H T V S GH GV : ℂ) :
    ((H + V) + T) - (GH + GV) =
      ((H + T) - S) + (S - GH) + (V - GV) := by
  calc
    ((H + V) + T) - (GH + GV)
        = ((H + T) + V) - (GH + GV) := by
          rw [add_assoc H V T]
          rw [add_comm V T]
          rw [← add_assoc H T V]
    _ = ((H + T) - GH) + (V - GV) := by
          exact add_sub_add_comm (H + T) V GH GV
    _ = (((H + T) - S) + (S - GH)) + (V - GV) := by
          rw [sub_eq_sub_add_add_sub (H + T) S GH]

/-- A finite sum with a tail term minus a second finite sum splits into the
sum of pointwise differences plus the tail term. -/
theorem finset_sum_add_tail_sub_sum_eq_sum_sub_add_tail
    {ι : Type*}
    (s : Finset ι)
    (A B : ι → ℂ)
    (T : ℂ) :
    ((∑ i in s, A i) + T) - (∑ i in s, B i) =
      (∑ i in s, A i - B i) + T := by
  calc
    ((∑ i in s, A i) + T) - (∑ i in s, B i)
        = ((∑ i in s, A i) - (∑ i in s, B i)) + T := by
          rw [sub_eq_add_neg]
          rw [sub_eq_add_neg]
          exact add_right_comm (∑ i in s, A i) T (-(∑ i in s, B i))
    _ = (∑ i in s, A i - B i) + T := by
          rw [Finset.sum_sub_distrib]

/-- Pulling a common nonnegative scalar through a finite sum plus one tail
term.  This is the algebraic normalization used by the horizontal connector
length estimate. -/
theorem finset_sum_const_mul_add_const_mul_eq_mul_sum_add
    {ι : Type*}
    (s : Finset ι)
    (η : ℝ)
    (a : ι → ℝ)
    (b : ℝ) :
    (∑ i in s, η * a i) + η * b =
      η * ((∑ i in s, a i) + b) := by
  calc
    (∑ i in s, η * a i) + η * b
        = η * (∑ i in s, a i) + η * b := by
          rw [Finset.mul_sum]
    _ = η * ((∑ i in s, a i) + b) := by
          rw [mul_add]

/-- Pulling one fixed scalar factor through a finite sum. -/
theorem finset_sum_const_mul_eq_mul_sum
    {ι : Type*}
    (s : Finset ι)
    (η : ℝ)
    (a : ι → ℝ) :
    (∑ i in s, η * a i) =
      η * (∑ i in s, a i) := by
  calc
    (∑ i in s, η * a i)
        = η * (∑ i in s, a i) := by
          rw [Finset.mul_sum]

/-- Pulling two fixed scalar factors through a finite sum. -/
theorem finset_sum_two_const_mul_eq_mul_mul_sum
    {ι : Type*}
    (s : Finset ι)
    (η ρ : ℝ)
    (a : ι → ℝ) :
    (∑ i in s, η * ρ * a i) =
      η * ρ * (∑ i in s, a i) := by
  calc
    (∑ i in s, η * ρ * a i)
        = (η * ρ) * (∑ i in s, a i) := by
          rw [Finset.mul_sum]
    _ = η * ρ * (∑ i in s, a i) := rfl

/-- The final scalar normalization for the angle-grid chord estimate. -/
theorem eta_mul_radius_mul_pi_eq_eta_mul_pi_mul_radius
    (η ρ : ℝ) :
    η * ρ * Real.pi = η * (Real.pi * ρ) := by
  calc
    η * ρ * Real.pi = η * (ρ * Real.pi) := mul_assoc η ρ Real.pi
    _ = η * (Real.pi * ρ) := by
          rw [mul_comm ρ Real.pi]

/-- The midpoint index of the one-cell staircase is zero. -/
theorem one_div_two_nat_eq_zero :
    (1 : ℕ) / 2 = 0 := by
  have hone_lt_two : (1 : ℕ) < 2 := by
    exact Nat.lt_succ_self 1
  exact Nat.div_eq_of_lt hone_lt_two

/-- The midpoint index of the one-cell staircase is at most the only index. -/
theorem one_div_two_nat_le_zero :
    (1 : ℕ) / 2 ≤ 0 := by
  exact le_of_eq one_div_two_nat_eq_zero

/-- A successor plus one is bounded by twice the successor. -/
theorem nat_succ_succ_le_two_mul_succ
    (n : ℕ) :
    n + 2 ≤ 2 * (n + 1) := by
  have hone_le_succ : 1 ≤ n + 1 := by
    exact Nat.succ_pos n
  calc
    n + 2 = n + 1 + 1 := rfl
    _ ≤ n + 1 + (n + 1) := by
      exact Nat.add_le_add_left hone_le_succ (n + 1)
    _ = 2 * (n + 1) := by
      exact (two_mul (n + 1)).symm

/-- The midpoint index of the staircase lies in the staircase range. -/
theorem nat_staircase_midpoint_le
    (m : ℕ) :
    (m + 1) / 2 ≤ m := by
  cases m with
  | zero =>
      exact one_div_two_nat_le_zero
  | succ n =>
      exact Nat.div_le_of_le_mul' (nat_succ_succ_le_two_mul_succ n)

/-- The suffix starting after `j` ends at `m+1` when `j ≤ m`. -/
theorem nat_succ_add_sub_eq_succ
    {j m : ℕ}
    (hjm : j ≤ m) :
    j + 1 + (m - j) = m + 1 := by
  calc
    j + 1 + (m - j) = j + (m - j) + 1 := by
      exact Nat.add_right_comm j 1 (m - j)
    _ = m + 1 := by
      rw [Nat.add_sub_cancel' hjm]

/-- The first suffix index is strictly beyond the midpoint. -/
theorem nat_lt_succ_add
    (j t : ℕ) :
    j < j + 1 + t := by
  calc
    j < j + 1 := Nat.lt_succ_self j
    _ ≤ j + 1 + t := Nat.le_add_right (j + 1) t

/-- A one-cell suffix length may be written in successor form. -/
theorem nat_one_add_eq_add_one
    (n : ℕ) :
    1 + n = n + 1 := by
  exact Nat.add_comm 1 n

/-- Reindexing identity for the one-cell suffix after `j`. -/
theorem nat_midpoint_suffix_index_assoc
    (j t : ℕ) :
    j + (t + 1) = j + 1 + t := by
  calc
    j + (t + 1) = j + (1 + t) := by
      rw [Nat.add_comm t 1]
    _ = j + 1 + t := by
      exact (Nat.add_assoc j 1 t).symm

/-- The right-semicircle angle interval has total length `π`. -/
theorem pi_div_two_sub_neg_pi_div_two :
    Real.pi / 2 - (-(Real.pi / 2)) = Real.pi := by
  calc
    Real.pi / 2 - (-(Real.pi / 2))
        = Real.pi / 2 + Real.pi / 2 := sub_neg_eq_add _ _
    _ = Real.pi := by
          rw [← two_mul (Real.pi / 2)]
          exact mul_div_cancel_left₀ Real.pi (two_ne_zero' ℝ)

/-- The `dx` integrand error factors by right distributivity. -/
theorem rightSemicircleAngle_dx_cell_integrand_error_factor
    (A B C : ℂ) :
    A * C - B * C = (A - B) * C :=
  (sub_mul A B C).symm

/-- Real scalar multiplication on `ℂ` can be read as right multiplication by
the corresponding real scalar. -/
theorem complex_real_smul_eq_mul_right
    (A : ℂ)
    (r : ℝ) :
    r • A = A * ((r : ℝ) : ℂ) := by
  rw [Complex.real_smul]
  exact mul_comm ((r : ℝ) : ℂ) A

/-- Multiplication by `I` factors out of a difference. -/
theorem Complex.I_mul_sub_factor
    (A B : ℂ) :
    Complex.I * A - Complex.I * B =
      Complex.I * (A - B) :=
  (mul_sub Complex.I A B).symm

/-- Scalar rearrangement behind one safe-endpoint cell comparison. -/
theorem real_safe_endpoint_cell_error_scalar
    (safe prev rnext rcur : ℝ) :
    (safe - prev) - (rnext - rcur) =
      (safe - rnext) - (prev - rcur) := by
  exact sub_sub_sub_comm safe prev rnext rcur

/-- One cell of the safe-endpoint comparison is just the difference between
two right-endpoint defects. -/
theorem safe_endpoint_cell_error_algebra
    (A : ℂ)
    (safe prev rnext rcur : ℝ) :
    A * (((safe - prev : ℝ) : ℂ)) -
        A * (((rnext - rcur : ℝ) : ℂ)) =
      A * (((safe - rnext : ℝ) : ℂ)) -
        A * (((prev - rcur : ℝ) : ℂ)) := by
  calc
    A * (((safe - prev : ℝ) : ℂ)) -
        A * (((rnext - rcur : ℝ) : ℂ))
        =
      A * ((((safe - prev) - (rnext - rcur) : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_sub]
      exact (mul_sub A ((safe - prev : ℝ) : ℂ) ((rnext - rcur : ℝ) : ℂ)).symm
    _ =
      A * ((((safe - rnext) - (prev - rcur) : ℝ) : ℂ)) := by
      rw [real_safe_endpoint_cell_error_scalar]
    _ =
      A * (((safe - rnext : ℝ) : ℂ)) -
        A * (((prev - rcur : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_sub]
      exact mul_sub A ((safe - rnext : ℝ) : ℂ) ((prev - rcur : ℝ) : ℂ)

/-- Pointwise expansion of one endpoint-defect summation-by-parts term. -/
theorem endpoint_defect_term_sub_mul
    (g e : ℕ → ℂ)
    (k : ℕ) :
    (g k - g (k + 1)) * e k =
      g k * e k - g (k + 1) * e k :=
  sub_mul (g k) (g (k + 1)) (e k)

/-- Sum expansion for endpoint-defect summation by parts. -/
theorem endpoint_defect_sum_terms_eq_sub_sums
    (m : ℕ)
    (g e : ℕ → ℂ) :
    (∑ k in Finset.range (m + 1), (g k - g (k + 1)) * e k) =
      (∑ k in Finset.range (m + 1), g k * e k) -
        ∑ k in Finset.range (m + 1), g (k + 1) * e k := by
  calc
    (∑ k in Finset.range (m + 1), (g k - g (k + 1)) * e k)
        =
      ∑ k in Finset.range (m + 1),
        (g k * e k - g (k + 1) * e k) := by
      exact
        Finset.sum_congr rfl
          (fun k _hk => endpoint_defect_term_sub_mul g e k)
    _ =
      (∑ k in Finset.range (m + 1), g k * e k) -
        ∑ k in Finset.range (m + 1), g (k + 1) * e k :=
      Finset.sum_sub_distrib

/-- The shifted endpoint-defect sum over `m+1` terms splits off its final
endpoint. -/
theorem endpoint_defect_shifted_sum_range_succ
    (m : ℕ)
    (g e : ℕ → ℂ) :
    (∑ k in Finset.range (m + 1), g (k + 1) * e k) =
      (∑ k in Finset.range m, g (k + 1) * e k) +
        g (m + 1) * e m :=
  Finset.sum_range_succ (fun k => g (k + 1) * e k) m

/-- Subtracting the shifted endpoint sum is the same as subtracting its
finite part and then its final endpoint. -/
theorem endpoint_defect_sub_shifted_sum
    (m : ℕ)
    (g e : ℕ → ℂ) :
    (∑ k in Finset.range (m + 1), g k * e k) -
        (∑ k in Finset.range m, g (k + 1) * e k) -
        g (m + 1) * e m =
      (∑ k in Finset.range (m + 1), g k * e k) -
        ((∑ k in Finset.range m, g (k + 1) * e k) +
          g (m + 1) * e m) :=
  sub_sub
    (∑ k in Finset.range (m + 1), g k * e k)
    (∑ k in Finset.range m, g (k + 1) * e k)
    (g (m + 1) * e m)

/-- Finite summation by parts for the endpoint-defect sequence.  This is the
pure algebraic form of the horizontal sample error telescope. -/
theorem endpoint_defect_summation_by_parts_algebra
    (m : ℕ)
    (g e : ℕ → ℂ) :
    (∑ k in Finset.range (m + 1), g k * e k) -
        (∑ k in Finset.range m, g (k + 1) * e k) -
        g (m + 1) * e m =
      ∑ k in Finset.range (m + 1), (g k - g (k + 1)) * e k := by
  calc
    (∑ k in Finset.range (m + 1), g k * e k) -
        (∑ k in Finset.range m, g (k + 1) * e k) -
        g (m + 1) * e m
        =
      (∑ k in Finset.range (m + 1), g k * e k) -
        ((∑ k in Finset.range m, g (k + 1) * e k) +
          g (m + 1) * e m) :=
      endpoint_defect_sub_shifted_sum m g e
    _ =
      (∑ k in Finset.range (m + 1), g k * e k) -
        ∑ k in Finset.range (m + 1), g (k + 1) * e k := by
      exact
        congrArg
          (fun z =>
            (∑ k in Finset.range (m + 1), g k * e k) - z)
          (endpoint_defect_shifted_sum_range_succ m g e).symm
    _ =
      ∑ k in Finset.range (m + 1), (g k - g (k + 1)) * e k :=
      (endpoint_defect_sum_terms_eq_sub_sums m g e).symm

/-- The top connector's `0 - safe` scalar is the negative of the corresponding
endpoint-defect scalar. -/
theorem top_connector_scalar_eq_neg_endpoint_defect_scalar
    (A : ℂ)
    (B : ℝ) :
    A * (((0 - B : ℝ) : ℂ)) =
      -A * (((B - 0 : ℝ) : ℂ)) := by
  calc
    A * (((0 - B : ℝ) : ℂ))
        = A * (-(B : ℂ)) := by
          rw [zero_sub, Complex.ofReal_neg]
    _ = -(A * (B : ℂ)) := mul_neg A (B : ℂ)
    _ = -A * (B : ℂ) := (neg_mul A (B : ℂ)).symm
    _ = -A * (((B - 0 : ℝ) : ℂ)) := by
          rw [sub_zero]

/-- The right semicircle graph coordinate agrees with the cosine coordinate
under the angle parametrization on `[-π/2, π/2]`. -/
theorem Complex.rightSemicircleGraphRe_mul_sin_eq_mul_cos
    {ρ θ : ℝ}
    (hρ : 0 ≤ ρ)
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    Complex.rightSemicircleGraphRe ρ (ρ * Real.sin θ) = ρ * Real.cos θ := by
  have hθIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact mem_rightSemicircleAngle_Icc_of_mem_uIcc hθ
  have hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθIcc
  have hmul_nonneg : 0 ≤ ρ * Real.cos θ :=
    mul_nonneg hρ hcos_nonneg
  dsimp [Complex.rightSemicircleGraphRe]
  have hrad :
      ρ ^ 2 - (ρ * Real.sin θ) ^ 2 = (ρ * Real.cos θ) ^ 2 := by
    exact radius_sq_sub_radius_mul_sin_sq_eq_radius_mul_cos_sq ρ θ
  rw [hrad]
  exact Real.sqrt_sq hmul_nonneg

/-- On the right semicircle angle range, the graph and angle parametrizations
describe the same point. -/
theorem Complex.rightSemicircleGraphPoint_eq_angle
    (c : ℂ)
    {ρ θ : ℝ}
    (hρ : 0 < ρ)
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ) =
      c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) := by
  have hgraph :
      Complex.rightSemicircleGraphRe ρ (ρ * Real.sin θ) = ρ * Real.cos θ :=
    Complex.rightSemicircleGraphRe_mul_sin_eq_mul_cos hρ.le hθ
  ext <;>
    simp [Complex.rightSemicircleGraphPoint, hgraph, Complex.exp_mul_I,
      mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc]

/-- The graph point at a height-grid point is the corresponding angle point. -/
theorem Complex.rightSemicircleGraphPoint_eq_angleGrid
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k) =
      c + (ρ : ℂ) *
        Complex.exp (Complex.I *
          (Complex.rightSemicircleAngleGrid ρ m k : ℂ)) := by
  have hsin :
      ρ * Real.sin (Complex.rightSemicircleAngleGrid ρ m k) =
        Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleAngleGrid_sin hρ hk
  have hθ :
      Complex.rightSemicircleAngleGrid ρ m k ∈
        [[-(Real.pi / 2), Real.pi / 2]] := by
    exact rightSemicircleAngle_uIcc_eq_Icc.symm ▸
      Complex.rightSemicircleAngleGrid_mem_Icc hρ hk
  rw [← hsin]
  exact Complex.rightSemicircleGraphPoint_eq_angle c hρ hθ

/-- The graph real coordinate at an angle-grid point is `ρ cos θ`. -/
theorem Complex.rightSemicircleGraphRe_eq_angleGrid_cos
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) =
      ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) := by
  have hsin :
      ρ * Real.sin (Complex.rightSemicircleAngleGrid ρ m k) =
        Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleAngleGrid_sin hρ hk
  have hθ :
      Complex.rightSemicircleAngleGrid ρ m k ∈
        [[-(Real.pi / 2), Real.pi / 2]] := by
    exact rightSemicircleAngle_uIcc_eq_Icc.symm ▸
      Complex.rightSemicircleAngleGrid_mem_Icc hρ hk
  rw [← hsin]
  exact Complex.rightSemicircleGraphRe_mul_sin_eq_mul_cos hρ.le hθ

/-- The graph-coordinate horizontal sample sum is the angle-grid chord sum. -/
theorem Complex.rightSemicircleGraphHorizontalSampleSum_eq_angleChordSum
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m =
      ∑ k in Finset.range (m + 1),
        f (c + (ρ : ℂ) *
          Complex.exp (Complex.I *
            (Complex.rightSemicircleAngleGrid ρ m k : ℂ))) *
        (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
           ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)) := by
  dsimp [Complex.rightSemicircleGraphHorizontalSampleSum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  rw [Complex.rightSemicircleGraphPoint_eq_angleGrid c hρ hk0]
  rw [Complex.rightSemicircleGraphRe_eq_angleGrid_cos hρ hk1]
  rw [Complex.rightSemicircleGraphRe_eq_angleGrid_cos hρ hk0]

/-- The angle-parametrized right semicircle lies in the deleted right-half
collar core. -/
theorem Complex.rightSemicircleAnglePoint_mem_core
    (c : ℂ)
    {ρ θ : ℝ}
    (hρ : 0 < ρ)
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hθIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    exact mem_rightSemicircleAngle_Icc_of_mem_uIcc hθ
  have hy : ρ * Real.sin θ ∈ Set.Icc (-ρ) ρ := by
    exact radius_mul_sin_mem_height_Icc hρ.le
  have hgraph_mem :
      Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ) ∈
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ :=
    Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
  have hpoint :
      Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ) =
        c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
    Complex.rightSemicircleGraphPoint_eq_angle c hρ hθ
  exact hpoint ▸ hgraph_mem

/-- The angle-parametrized right-semicircle probe is continuous on the angle
interval. -/
theorem Complex.continuousOn_rightSemicircleAngleProbe
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    ContinuousOn
      (fun θ : ℝ =>
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hparam :
      ContinuousOn
        (fun θ : ℝ =>
          c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (continuous_const.add
      (continuous_const.mul
        (Complex.continuous_exp.comp
          (continuous_const.mul continuous_ofReal)))).continuousOn
  have hmaps :
      MapsTo
        (fun θ : ℝ =>
          c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro θ hθ
    exact
      Complex.rightSemicircleAnglePoint_mem_core c hρ
        (rightSemicircleAngle_uIcc_eq_Icc.symm ▸ hθ)
  exact hcont.comp_continuousOn hparam hmaps

/-- The angle `dx` integrand is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleAngle_dx
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun θ : ℝ =>
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (((-ρ * Real.sin θ : ℝ) : ℂ)))
      volume
      (-(Real.pi / 2))
      (Real.pi / 2) := by
  have hprobe :=
    Complex.continuousOn_rightSemicircleAngleProbe f c hρ hcont
  have hdx :
      ContinuousOn
        (fun θ : ℝ => (((-ρ * Real.sin θ : ℝ) : ℂ)))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (continuous_ofReal.comp
      (continuous_const.mul continuous_sin)).continuousOn
  exact (hprobe.mul hdx).intervalIntegrable

/-- The angle `dy` integrand is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleAngle_dy
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun θ : ℝ =>
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          ((ρ * Real.cos θ : ℝ) : ℂ))
      volume
      (-(Real.pi / 2))
      (Real.pi / 2) := by
  have hprobe :=
    Complex.continuousOn_rightSemicircleAngleProbe f c hρ hcont
  have hdy :
      ContinuousOn
        (fun θ : ℝ => ((ρ * Real.cos θ : ℝ) : ℂ))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    (continuous_ofReal.comp
      (continuous_const.mul continuous_cos)).continuousOn
  exact (hprobe.mul hdy).intervalIntegrable

/-- Scalar change of variables from the vertical graph coordinate
`y = ρ sin θ` to the angle coordinate on the right semicircle. -/
theorem Complex.rightSemicircleGraphScalarIntegral_eq_angle_dy
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∫ y : ℝ in (-ρ)..ρ,
      f (Complex.rightSemicircleGraphPoint c ρ y)) =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          ((ρ * Real.cos θ : ℝ) : ℂ) := by
  let a : ℝ := -(Real.pi / 2)
  let b : ℝ := Real.pi / 2
  let φ : ℝ → ℝ := fun θ => ρ * Real.sin θ
  let G : ℝ → ℂ := fun y => f (Complex.rightSemicircleGraphPoint c ρ y)
  have hφ_deriv :
      ∀ θ ∈ [[a, b]], HasDerivAt φ (ρ * Real.cos θ) θ := by
    intro θ _hθ
    dsimp [φ]
    exact (Real.hasDerivAt_sin θ).const_mul ρ
  have hφ_deriv_cont :
      ContinuousOn (fun θ : ℝ => ρ * Real.cos θ) [[a, b]] := by
    exact (continuous_const.mul continuous_cos).continuousOn
  have hG_base :
      ContinuousOn G (Set.Icc (-ρ) ρ) := by
    dsimp [G]
    exact
      Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
        f c hρ hcont
  have hG_image :
      ContinuousOn G (φ '' [[a, b]]) := by
    refine hG_base.mono ?_
    intro y hy
    rcases hy with ⟨θ, _hθ, rfl⟩
    dsimp [φ]
    exact radius_mul_sin_mem_height_Icc hρ.le
  have hsubst :
      (∫ θ : ℝ in a..b, (ρ * Real.cos θ) • (G (φ θ))) =
        ∫ y : ℝ in φ a..φ b, G y := by
    exact
      intervalIntegral.integral_comp_smul_deriv'
        (a := a) (b := b)
        (f := φ) (f' := fun θ => ρ * Real.cos θ)
        (g := G)
        hφ_deriv hφ_deriv_cont hG_image
  have hφa : φ a = -ρ := by
    dsimp [φ, a]
    exact radius_mul_sin_neg_pi_div_two ρ
  have hφb : φ b = ρ := by
    dsimp [φ, b]
    exact radius_mul_sin_pi_div_two ρ
  calc
    (∫ y : ℝ in (-ρ)..ρ, G y) =
        ∫ y : ℝ in φ a..φ b, G y := by
      rw [hφa, hφb]
    _ = ∫ θ : ℝ in a..b, (ρ * Real.cos θ) • (G (φ θ)) :=
      hsubst.symm
    _ =
        ∫ θ : ℝ in a..b,
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      dsimp [G, φ]
      have hpoint :
          Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ) =
            c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
        Complex.rightSemicircleGraphPoint_eq_angle c hρ hθ
      rw [hpoint]
      exact
        complex_real_smul_eq_mul_right
          (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          (ρ * Real.cos θ)

/-- The vertical graph integral is the `I dy` component of the angle
parametrization. -/
theorem Complex.rightSemicircleGraphVerticalIntegral_eq_angle_dy
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightSemicircleGraphVerticalIntegral f c ρ =
      Complex.I *
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ) := by
  dsimp [Complex.rightSemicircleGraphVerticalIntegral]
  rw [Complex.rightSemicircleGraphScalarIntegral_eq_angle_dy f c hρ hcont]

/-- The angle-parametrized right-semicircle integral decomposes into its
horizontal `dx` part and vertical `I dy` part. -/
theorem Complex.rightSemicircleAngleIntegral_eq_angle_dx_add_angle_dy
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightSemicircleAngleIntegral f c ρ =
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (((-ρ * Real.sin θ : ℝ) : ℂ))) +
      Complex.I *
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ)) := by
  let Fx : ℝ → ℂ := fun θ =>
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      (((-ρ * Real.sin θ : ℝ) : ℂ))
  let Fy : ℝ → ℂ := fun θ =>
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
      ((ρ * Real.cos θ : ℝ) : ℂ)
  have hFx : IntervalIntegrable Fx volume (-(Real.pi / 2)) (Real.pi / 2) :=
    Complex.intervalIntegrable_rightSemicircleAngle_dx f c hρ hcont
  have hFy : IntervalIntegrable Fy volume (-(Real.pi / 2)) (Real.pi / 2) :=
    Complex.intervalIntegrable_rightSemicircleAngle_dy f c hρ hcont
  have hpoint :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) *
            Complex.exp (Complex.I * (θ : ℂ)))) =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Fx θ + Complex.I * Fy θ := by
    apply intervalIntegral.integral_congr
    intro θ _hθ
    dsimp [Fx, Fy]
    exact
      rightSemicircleAngle_tangentFactor_decompose
        (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ρ θ
  dsimp [Complex.rightSemicircleAngleIntegral]
  rw [hpoint]
  rw [intervalIntegral.integral_add hFx (hFy.const_mul Complex.I)]
  rw [intervalIntegral.integral_const_mul]
  rfl

/-- The graph-horizontal target is the nonzero `dx` component of the angle
parametrization. -/
theorem Complex.rightSemicircleGraphHorizontalIntegral_eq_angle_dx
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightSemicircleGraphHorizontalIntegral f c ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (((-ρ * Real.sin θ : ℝ) : ℂ)) := by
  have hangle :=
    Complex.rightSemicircleAngleIntegral_eq_angle_dx_add_angle_dy
      f c hρ hcont
  have hvertical :=
    Complex.rightSemicircleGraphVerticalIntegral_eq_angle_dy
      f c hρ hcont
  dsimp [Complex.rightSemicircleGraphHorizontalIntegral]
  rw [hangle, hvertical]
  exact horizontal_component_eq_of_sum_eq_add_vertical rfl

/-- Uniform approximation of the circular graph by the exterior staircase
safe real coordinate on each height cell. -/
theorem Complex.rightSemicircleStaircaseSafeRe_uniform_approx_graphRe
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ ε > 0,
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleGraphRe ρ y‖ < ε := by
  have hgraph_cont :
      ContinuousOn
        (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphRe_Icc hρ
  have hgraph_uniform :
      UniformContinuousOn
        (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
        (Set.Icc (-ρ) ρ) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hgraph_cont
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hgraph_uniform ε hε) with
    ⟨δ, hδ, hδ_modulus⟩
  have hmesh :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| < δ :=
    Complex.eventually_rightSemicircleStaircase_cell_length_lt hρ hδ
  filter_upwards [hmesh] with m hm k hk y hy
  rcases
      Complex.exists_rightSemicircleStaircaseSafeRe_eq_graphRe_of_cell
        hρ m k hk with
    ⟨yₛ, hyₛ_cell, hsafe⟩
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
  have cell_subset :
      [[Complex.rightSemicircleStaircaseY ρ m k,
        Complex.rightSemicircleStaircaseY ρ m (k + 1)]] ⊆
        Set.Icc (-ρ) ρ := by
    intro u hu
    have hu_height :
        u ∈ [[-ρ, ρ]] :=
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hu
    have hu_eq : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
      Set.uIcc_of_le (Complex.neg_radius_le_radius hρ.le)
    exact hu_eq ▸ hu_height
  have hy_Icc : y ∈ Set.Icc (-ρ) ρ := cell_subset hy
  have hyₛ_Icc : yₛ ∈ Set.Icc (-ρ) ρ := cell_subset hyₛ_cell
  have hdist_cell :
      dist y yₛ < δ := by
    have hdist_le :
        dist y yₛ ≤
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| :=
      Complex.dist_le_rightSemicircleStaircase_cell_length_of_mem
        ρ m k hy hyₛ_cell
    exact lt_of_le_of_lt hdist_le (hm k hk)
  have hgraph_close :
      dist
        (Complex.rightSemicircleGraphRe ρ y)
        (Complex.rightSemicircleGraphRe ρ yₛ) < ε :=
    hδ_modulus y hy_Icc yₛ hyₛ_Icc hdist_cell
  rw [hsafe]
  simpa [Real.dist_eq, abs_sub_comm] using hgraph_close

/-- The previous safe coordinate uniformly approximates the current graph
coordinate at the bottom sample of each horizontal connector. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_uniform_approx_graphRe
    {ρ : ℝ}
    (hρ : 0 < ρ) :
    ∀ ε > 0,
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ‖Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k)‖ < ε := by
  intro ε hε
  have hsafe :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleGraphRe ρ y‖ < ε :=
    Complex.rightSemicircleStaircaseSafeRe_uniform_approx_graphRe hρ ε hε
  filter_upwards [hsafe] with m hm k hk
  by_cases hk0 : k = 0
  · subst k
    rw [Complex.rightSemicircleStaircasePrevSafeRe_zero]
    have hy0 : Complex.rightSemicircleStaircaseY ρ m 0 = -ρ :=
      Complex.rightSemicircleStaircaseY_zero ρ m
    rw [hy0, Complex.rightSemicircleGraphRe_bottom, sub_zero, norm_zero]
    exact hε
  ·
    have hk_pred : k - 1 ∈ Finset.range (m + 1) := by
      exact Complex.staircase_pred_mem_range_of_ne_zero hk hk0
    have hsucc : (k - 1) + 1 = k :=
      Complex.staircase_pred_succ_of_ne_zero hk0
    have hy_mem :
        Complex.rightSemicircleStaircaseY ρ m k ∈
          [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
            Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)]] := by
      rw [hsucc]
      exact right_mem_uIcc
    have happrox :=
      hm (k - 1) hk_pred
        (Complex.rightSemicircleStaircaseY ρ m k) hy_mem
    simpa [Complex.rightSemicircleStaircasePrevSafeRe, hk0] using happrox

/-- Distance from a staircase vertical side point to the matching graph point
is exactly the horizontal graph-coordinate error. -/
theorem Complex.dist_rightSemicircleStaircasePoint_graphPoint
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ)
    (y : ℝ) :
    dist
      ((((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ y) =
    ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
      Complex.rightSemicircleGraphRe ρ y‖ := by
  have hdist :=
    Complex.dist_realLinePoint_rightSemicircleGraphPoint
      c ρ (Complex.rightSemicircleStaircaseSafeRe ρ m k) y
  simpa [Real.norm_eq_abs] using hdist

/-- A horizontal connector point is close to the graph sample if both endpoint
safe coordinates are close to that graph real-coordinate. -/
theorem Complex.dist_rightSemicircleHorizontalPoint_graphPoint_le
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ)
    {x δ : ℝ}
    (hδ : 0 ≤ δ)
    (hx :
      x ∈
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]])
    (hprev :
      ‖Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ)
    (hsafe :
      ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ) :
    dist
      ((((c.re + x : ℝ) : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k))
      ≤ δ := by
  let g : ℝ :=
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  have hprev_abs :
      |Complex.rightSemicircleStaircasePrevSafeRe ρ m k - g| ≤ δ := by
    simpa [Real.norm_eq_abs, g] using hprev
  have hsafe_abs :
      |Complex.rightSemicircleStaircaseSafeRe ρ m k - g| ≤ δ := by
    simpa [Real.norm_eq_abs, g] using hsafe
  have hx_bounds : g - δ ≤ x ∧ x ≤ g + δ := by
    exact
      abs_sub_le_iff.mp
        (abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le hx hprev_abs hsafe_abs)
  have hx_abs : |x - g| ≤ δ := by
    exact abs_sub_le_iff.mpr hx_bounds
  have hdist :
      dist
        ((((c.re + x : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m k)) =
        |x - g| := by
    simpa [g] using
      (Complex.dist_realLinePoint_rightSemicircleGraphPoint
        c ρ x (Complex.rightSemicircleStaircaseY ρ m k))
  rw [hdist]
  exact hx_abs

/-- A top horizontal connector point is close to the top graph point if its
safe endpoint is close to the top graph real-coordinate. -/
theorem Complex.dist_rightSemicircleTopConnectorPoint_graphPoint_le
    (c : ℂ)
    {ρ : ℝ}
    (m : ℕ)
    {x δ : ℝ}
    (hδ : 0 ≤ δ)
    (hx : x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]])
    (hsafe :
      ‖Complex.rightSemicircleStaircaseSafeRe ρ m m -
        Complex.rightSemicircleGraphRe ρ ρ‖ ≤ δ) :
    dist
      ((((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + ρ : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ ρ)
      ≤ δ := by
  have hzero : Complex.rightSemicircleGraphRe ρ ρ = 0 :=
    Complex.rightSemicircleGraphRe_top
  have hsafe_abs : |Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ δ := by
    simpa [Real.norm_eq_abs, hzero, sub_zero] using hsafe
  have hsafe_abs_zero :
      |Complex.rightSemicircleStaircaseSafeRe ρ m m - 0| ≤ δ := by
    simpa [sub_zero] using hsafe_abs
  have hzero_abs_zero : |(0 : ℝ) - 0| ≤ δ := by
    simpa using hδ
  have hx_abs : |x| ≤ δ := by
    have hx_abs_zero :
        |x - 0| ≤ δ :=
      abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le
        hx hsafe_abs_zero hzero_abs_zero
    simpa [sub_zero] using hx_abs_zero
  have hdist :
      dist
        ((((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        (Complex.rightSemicircleGraphPoint c ρ ρ) =
        |x| := by
    have hraw :=
      Complex.dist_realLinePoint_rightSemicircleGraphPoint c ρ x ρ
    simpa [hzero, sub_zero] using hraw
  rw [hdist]
  exact hx_abs

/-- Uniform approximation of the vertical staircase integrand by the graph
integrand. -/
theorem Complex.rightSemicircleVerticalIntegrand_uniform_approx_graph
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    ∀ ε > 0,
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                  Complex.I * (((c.im + y : ℝ) : ℂ))) -
              f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ ε := by
  have hf_uniform :
      UniformContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    Complex.uniformContinuousOn_rightHalfRectangleDeletedDiskCoreDomain_self
      f c hρ hcont
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hf_uniform ε hε) with
    ⟨δ, hδ, hδ_modulus⟩
  have hsafe :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleGraphRe ρ y‖ < δ :=
    Complex.rightSemicircleStaircaseSafeRe_uniform_approx_graphRe
      hρ δ hδ
  filter_upwards [hsafe] with m hm k hk y hy
  let zₛ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + y : ℝ) : ℂ)))
  let zᵧ : ℂ := Complex.rightSemicircleGraphPoint c ρ y
  have hzₛ :
      zₛ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [zₛ]
    exact Complex.rightSemicircleStaircaseVertical_subset_core
      c hρ m k hk hy
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
  have hy_Icc : y ∈ Set.Icc (-ρ) ρ := by
    have hy_height :
        y ∈ [[-ρ, ρ]] :=
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hy
    have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
      Set.uIcc_of_le (Complex.neg_radius_le_radius hρ.le)
    exact huIcc ▸ hy_height
  have hzᵧ :
      zᵧ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [zᵧ]
    exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy_Icc
  have hdist :
      dist zₛ zᵧ < δ := by
    dsimp [zₛ, zᵧ]
    rw [Complex.dist_rightSemicircleStaircasePoint_graphPoint]
    exact hm k hk y hy
  have hclose : dist (f zₛ) (f zᵧ) < ε :=
    hδ_modulus zₛ hzₛ zᵧ hzᵧ hdist
  dsimp [zₛ, zᵧ] at hclose ⊢
  simpa [dist_eq_norm] using le_of_lt hclose

/-- One vertical staircase cell is controlled by the uniform integrand error
times its height. -/
theorem Complex.norm_rightSemicircleStaircaseVertical_cell_sub_graph_cell_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {η : ℝ}
    (happrox :
      ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
              Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
        ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))) -
          f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η) :
    ‖(∫ y : ℝ in
        Complex.rightSemicircleStaircaseY ρ m k..
          Complex.rightSemicircleStaircaseY ρ m (k + 1),
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (((c.im + y : ℝ) : ℂ))) -
          f (Complex.rightSemicircleGraphPoint c ρ y))‖
      ≤ η *
        |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k| := by
  exact
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun y hy =>
        happrox y (Set.uIoc_subset_uIcc hy))

/-- A uniform vertical-integrand error bounds the difference between the finite
vertical staircase sum and the graph vertical integral. -/
theorem Complex.norm_sum_rightSemicircleStaircaseVertical_sub_graphVertical_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ)
    {η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (happrox :
      ∀ k ∈ Finset.range (m + 1),
        ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
          ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                Complex.I * (((c.im + y : ℝ) : ℂ))) -
            f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η) :
    ‖(∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
      Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
      ≤ η * (2 * ρ) := by
  let S : ℕ → ℂ := fun k =>
    ∫ y : ℝ in
      Complex.rightSemicircleStaircaseY ρ m k..
        Complex.rightSemicircleStaircaseY ρ m (k + 1),
      f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ)))
  let G : ℕ → ℂ := fun k =>
    ∫ y : ℝ in
      Complex.rightSemicircleStaircaseY ρ m k..
        Complex.rightSemicircleStaircaseY ρ m (k + 1),
      f (Complex.rightSemicircleGraphPoint c ρ y)
  have hcell :
      ∀ k ∈ Finset.range (m + 1),
        ‖S k - G k‖ ≤
          η *
            |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
              Complex.rightSemicircleStaircaseY ρ m k| := by
    intro k hk
    have hS :
        IntervalIntegrable
          (fun y : ℝ =>
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))))
          volume
          (Complex.rightSemicircleStaircaseY ρ m k)
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
      Complex.intervalIntegrable_rightSemicircleStaircaseVertical
        f c hρ m k hk hcont
    have hG_full :
        IntervalIntegrable
          (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
          volume
          (-ρ)
          ρ :=
      Complex.intervalIntegrable_rightSemicircleGraphVertical f c hρ hcont
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk
    have hk1 : k + 1 ∈ Finset.range (m + 2) := by
      exact Complex.staircase_upper_sample_mem_range hk
    have hy0 :
        Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
    have hy1 :
        Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
    have hG :
        IntervalIntegrable
          (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
          volume
          (Complex.rightSemicircleStaircaseY ρ m k)
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
      Complex.intervalIntegrable_of_mem_uIcc hG_full hy0 hy1
    have hintegral :
        S k - G k =
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))) -
              f (Complex.rightSemicircleGraphPoint c ρ y) := by
      dsimp [S, G]
      rw [intervalIntegral.integral_sub hS hG]
    rw [hintegral]
    exact
      Complex.norm_rightSemicircleStaircaseVertical_cell_sub_graph_cell_le
        f c hρ hcont m k hk (happrox k hk)
  have hsum_error :
      ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖
        ≤ η * (2 * ρ) := by
    calc
      ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖
          = ‖∑ k in Finset.range (m + 1), (S k - G k)‖ := by
            rw [Finset.sum_sub_distrib]
      _ ≤ ∑ k in Finset.range (m + 1), ‖S k - G k‖ :=
            Finset.norm_sum_le _ _
      _ ≤
          ∑ k in Finset.range (m + 1),
            η *
              |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
                Complex.rightSemicircleStaircaseY ρ m k| := by
            exact Finset.sum_le_sum hcell
      _ =
          η *
            ∑ k in Finset.range (m + 1),
              |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
                Complex.rightSemicircleStaircaseY ρ m k| := by
            exact
              finset_sum_const_mul_eq_mul_sum
                (Finset.range (m + 1))
                η
                (fun k =>
                  |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
                    Complex.rightSemicircleStaircaseY ρ m k|)
      _ = η * (2 * ρ) := by
            rw [Complex.sum_rightSemicircleStaircase_cell_lengths hρ.le]
  have hstair :
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) =
        Complex.I * ∑ k in Finset.range (m + 1), S k := by
    dsimp [S]
    exact Complex.sum_rightSemicircleStaircaseVerticalIntegral_eq_I_mul_sum
      f c ρ m
  have hgraph :
      Complex.rightSemicircleGraphVerticalIntegral f c ρ =
        Complex.I * ∑ k in Finset.range (m + 1), G k := by
    dsimp [G]
    exact Complex.rightSemicircleGraphVerticalIntegral_eq_sum_cells
      f c hρ hcont m
  calc
    ‖(∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
      Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
        =
      ‖Complex.I *
        ((∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k))‖ := by
          rw [hstair, hgraph]
          exact
            congrArg norm
              (Complex.I_mul_sub_factor
                (∑ k in Finset.range (m + 1), S k)
                (∑ k in Finset.range (m + 1), G k))
    _ = ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖ := by
          rw [norm_mul, Complex.normSq_apply, Complex.normSq_I]
          simp
    _ ≤ η * (2 * ρ) := hsum_error

/-- Vertical staircase sides converge to the vertical part of the circular
graph integral. -/
theorem Complex.rightSemicircleStaircaseVerticalIntegral_tendsto_graphVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        ∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)
      atTop
      (𝓝 (Complex.rightSemicircleGraphVerticalIntegral f c ρ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htwoρ_pos : 0 < 2 * ρ :=
    real_two_mul_pos_of_pos hρ
  let η : ℝ := ε / (2 * ρ)
  have hη_pos : 0 < η := div_pos hε htwoρ_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hevent :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                  Complex.I * (((c.im + y : ℝ) : ℂ))) -
              f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η :=
    (Complex.rightSemicircleVerticalIntegrand_uniform_approx_graph
      f c hρ hcont η hη_pos)
  filter_upwards [hevent] with m hm
  have hbound :
      ‖(∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
        Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
        ≤ η * (2 * ρ) :=
    Complex.norm_sum_rightSemicircleStaircaseVertical_sub_graphVertical_le
      f c hρ hcont m hη_nonneg hm
  have hη_eq : η * (2 * ρ) = ε := by
    dsimp [η]
    exact div_mul_cancel_of_pos_right htwoρ_pos
  exact lt_of_le_of_lt hbound (by rw [hη_eq])

/-- Uniform approximation of the horizontal staircase integrand by its graph
sample value on every connector, including the final top connector. -/
theorem Complex.rightSemicircleHorizontalIntegrand_uniform_approx_sample
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    ∀ ε > 0,
      ∀ᶠ m : ℕ in atTop,
        (∀ k ∈ Finset.range (m + 1),
          ∀ x ∈
            [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
              Complex.rightSemicircleStaircaseSafeRe ρ m k]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I *
                    (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ
                  (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ ε) ∧
        (∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ ε) := by
  have hf_uniform :
      UniformContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    Complex.uniformContinuousOn_rightHalfRectangleDeletedDiskCoreDomain_self
      f c hρ hcont
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hf_uniform ε hε) with
    ⟨δ, hδ, hδ_modulus⟩
  let δ₀ : ℝ := δ / 2
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact half_pos hδ
  have hδ₀_nonneg : 0 ≤ δ₀ := le_of_lt hδ₀_pos
  have hδ₀_lt : δ₀ < δ := by
    dsimp [δ₀]
    exact half_lt_self hδ
  have hprev :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ‖Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k)‖ < δ₀ :=
    Complex.rightSemicircleStaircasePrevSafeRe_uniform_approx_graphRe
      hρ δ₀ hδ₀_pos
  have hsafe :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleGraphRe ρ y‖ < δ₀ :=
    Complex.rightSemicircleStaircaseSafeRe_uniform_approx_graphRe
      hρ δ₀ hδ₀_pos
  filter_upwards [hprev, hsafe] with m hm_prev hm_safe
  constructor
  · intro k hk x hx
    let zₓ : ℂ :=
      (((c.re + x : ℝ) : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
    let zᵧ : ℂ :=
      Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)
    have hzₓ :
        zₓ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      dsimp [zₓ]
      exact
        Complex.rightSemicircleStaircaseHorizontal_subset_core
          c hρ m k hk hx
    have hk_mem : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk
    have hy :
        Complex.rightSemicircleStaircaseY ρ m k ∈ Set.Icc (-ρ) ρ := by
      exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ.le
        (Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk_mem)
    have hzᵧ :
        zᵧ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      dsimp [zᵧ]
      exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
    have hsafe_at_sample :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ₀ := by
      have hy_sample :
          Complex.rightSemicircleStaircaseY ρ m k ∈
            [[Complex.rightSemicircleStaircaseY ρ m k,
              Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
        left_mem_uIcc
      exact le_of_lt (hm_safe k hk
        (Complex.rightSemicircleStaircaseY ρ m k) hy_sample)
    have hprev_at_sample :
        ‖Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ₀ :=
      le_of_lt (hm_prev k hk)
    have hdist_le :
        dist zₓ zᵧ ≤ δ₀ := by
      dsimp [zₓ, zᵧ]
      exact
        Complex.dist_rightSemicircleHorizontalPoint_graphPoint_le
          c ρ m k hδ₀_nonneg hx hprev_at_sample hsafe_at_sample
    have hdist_lt : dist zₓ zᵧ < δ :=
      lt_of_le_of_lt hdist_le hδ₀_lt
    have hclose : dist (f zₓ) (f zᵧ) < ε :=
      hδ_modulus zₓ hzₓ zᵧ hzᵧ hdist_lt
    dsimp [zₓ, zᵧ] at hclose ⊢
    simpa [dist_eq_norm] using le_of_lt hclose
  · intro x hx
    let zₓ : ℂ :=
      (((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + ρ : ℝ) : ℂ)))
    let zᵧ : ℂ := Complex.rightSemicircleGraphPoint c ρ ρ
    have hzₓ :
        zₓ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      dsimp [zₓ]
      exact
        Complex.rightSemicircleStaircaseTopConnector_subset_core
          c hρ m hx
    have hy : ρ ∈ Set.Icc (-ρ) ρ := by
      exact Complex.radius_mem_semicircle_height_Icc hρ.le
    have hzᵧ :
        zᵧ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      dsimp [zᵧ]
      exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
    have hm_mem : m ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range] using Nat.lt_succ_self m
    have hy_top :
        ρ ∈
          [[Complex.rightSemicircleStaircaseY ρ m m,
            Complex.rightSemicircleStaircaseY ρ m (m + 1)]] := by
      rw [Complex.rightSemicircleStaircaseY_last]
      exact right_mem_uIcc
    have hsafe_top :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m m -
          Complex.rightSemicircleGraphRe ρ ρ‖ ≤ δ₀ :=
      le_of_lt (hm_safe m hm_mem ρ hy_top)
    have hdist_le :
        dist zₓ zᵧ ≤ δ₀ := by
      dsimp [zₓ, zᵧ]
      exact
        Complex.dist_rightSemicircleTopConnectorPoint_graphPoint_le
          c m hδ₀_nonneg hx hsafe_top
    have hdist_lt : dist zₓ zᵧ < δ :=
      lt_of_le_of_lt hdist_le hδ₀_lt
    have hclose : dist (f zₓ) (f zᵧ) < ε :=
      hδ_modulus zₓ hzₓ zᵧ hzᵧ hdist_lt
    dsimp [zₓ, zᵧ] at hclose ⊢
    simpa [dist_eq_norm] using le_of_lt hclose

/-- The total horizontal variation of the exterior safe staircase is uniformly
bounded.  This is the geometric finite-variation input for horizontal
connector error estimates. -/
theorem Complex.sum_rightSemicircleStaircase_horizontal_connector_lengths_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k|)
      + |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m|
      ≤ 2 * ρ := by
  let j : ℕ := (m + 1) / 2
  have hjm : j ≤ m := by
    cases m with
    | zero =>
        dsimp [j]
        exact one_div_two_nat_le_zero
    | succ m =>
        dsimp [j]
        exact Nat.div_le_self (m + 2) 2
  exact
    Complex.rightSemicircleStaircaseSafeRe_totalHorizontalVariation_le_two_radius_of_unimodal
      hρ m j hjm
      (by
        dsimp [j]
        exact Complex.rightSemicircleStaircaseSafeRe_monotone_prefix_midpoint
          hρ m)
      (by
        dsimp [j]
        exact Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint
          hρ m)

/-- One horizontal staircase connector is controlled by its uniform integrand
error times its connector length. -/
theorem Complex.norm_rightSemicircleStaircaseHorizontal_cell_sub_sample_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {η : ℝ}
    (happrox :
      ∀ x ∈
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]],
        ‖f ((((c.re + x : ℝ) : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
          f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ η) :
    ‖Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k -
      f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m k)) *
        (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
           Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))‖
      ≤ η *
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k| := by
  let a : ℝ := Complex.rightSemicircleStaircasePrevSafeRe ρ m k
  let b : ℝ := Complex.rightSemicircleStaircaseSafeRe ρ m k
  let z₀ : ℂ :=
    Complex.rightSemicircleGraphPoint c ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  let F : ℝ → ℂ := fun x =>
    f ((((c.re + x : ℝ) : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
      f z₀
  have hmain :
      Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k -
        f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, F x := by
    dsimp [Complex.rightSemicircleStaircaseHorizontalIntegral, F, a, b, z₀]
    rw [intervalIntegral.integral_sub]
    · simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    · exact
        Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
          f c hρ m k hk hcont
    · exact intervalIntegrable_const
  rw [hmain]
  exact
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx =>
        happrox x (Set.uIoc_subset_uIcc hx))

/-- The final top horizontal connector is controlled by its uniform integrand
error times its connector length. -/
theorem Complex.norm_rightSemicircleStaircaseTopConnector_sub_sample_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ)
    {η : ℝ}
    (happrox :
      ∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
        ‖f ((((c.re + x : ℝ) : ℂ) +
              Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
          f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ η) :
    ‖Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m -
      f (Complex.rightSemicircleGraphPoint c ρ ρ) *
        (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))‖
      ≤ η * |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m| := by
  let a : ℝ := Complex.rightSemicircleStaircaseSafeRe ρ m m
  let b : ℝ := 0
  let z₀ : ℂ := Complex.rightSemicircleGraphPoint c ρ ρ
  let F : ℝ → ℂ := fun x =>
    f ((((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
      f z₀
  have hmain :
      Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m -
        f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, F x := by
    dsimp [Complex.rightSemicircleStaircaseTopConnectorIntegral, F, a, b, z₀]
    rw [intervalIntegral.integral_sub]
    · simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    · exact
        Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
          f c hρ m hcont
    · exact intervalIntegrable_const
  rw [hmain]
  exact
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx =>
        happrox x (Set.uIoc_subset_uIcc hx))

/-- A uniform horizontal-integrand error bounds the difference between the
finite horizontal connector sum and its graph-point finite-difference sample
sum. -/
theorem Complex.norm_sum_rightSemicircleStaircaseHorizontal_sub_sampleSum_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ)
    {η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (happrox :
      (∀ k ∈ Finset.range (m + 1),
        ∀ x ∈
          [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
            Complex.rightSemicircleStaircaseSafeRe ρ m k]],
          ‖f ((((c.re + x : ℝ) : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
            f (Complex.rightSemicircleGraphPoint c ρ
                (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ η) ∧
      (∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
          ‖f ((((c.re + x : ℝ) : ℂ) +
                Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
            f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ η)) :
    ‖((∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
      Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m‖
      ≤ η * (2 * ρ) := by
  let E : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k -
      f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m k)) *
        (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
           Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))
  let Etop : ℂ :=
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m -
      f (Complex.rightSemicircleGraphPoint c ρ ρ) *
        (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))
  have hdecomp :
      ((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m =
        (∑ k in Finset.range (m + 1), E k) + Etop := by
    dsimp [Complex.rightSemicircleStaircaseHorizontalSampleSum, E, Etop]
    rw [Finset.sum_sub_distrib]
    exact
      horizontal_top_sample_error_decompose
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k)
        (Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
        (∑ k in Finset.range (m + 1),
          f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
            (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
               Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)))
        (f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)))
  have hcell :
      ∀ k ∈ Finset.range (m + 1),
        ‖E k‖ ≤
          η *
            |Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k| := by
    intro k hk
    exact
      Complex.norm_rightSemicircleStaircaseHorizontal_cell_sub_sample_le
        f c hρ hcont m k hk (happrox.1 k hk)
  have htop :
      ‖Etop‖ ≤ η * |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m| :=
    Complex.norm_rightSemicircleStaircaseTopConnector_sub_sample_le
      f c hρ hcont m happrox.2
  have hnorm :
      ‖(∑ k in Finset.range (m + 1), E k) + Etop‖
        ≤ η *
          ((∑ k in Finset.range (m + 1),
              |Complex.rightSemicircleStaircaseSafeRe ρ m k -
                Complex.rightSemicircleStaircasePrevSafeRe ρ m k|)
            + |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m|) := by
    calc
      ‖(∑ k in Finset.range (m + 1), E k) + Etop‖
          ≤ ‖∑ k in Finset.range (m + 1), E k‖ + ‖Etop‖ :=
            norm_add_le _ _
      _ ≤ (∑ k in Finset.range (m + 1), ‖E k‖) + ‖Etop‖ := by
            exact add_le_add_right (Finset.norm_sum_le _ _) _
      _ ≤
          (∑ k in Finset.range (m + 1),
            η *
              |Complex.rightSemicircleStaircaseSafeRe ρ m k -
                Complex.rightSemicircleStaircasePrevSafeRe ρ m k|) +
            η * |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m| := by
            exact add_le_add (Finset.sum_le_sum hcell) htop
      _ =
          η *
            ((∑ k in Finset.range (m + 1),
              |Complex.rightSemicircleStaircaseSafeRe ρ m k -
                Complex.rightSemicircleStaircasePrevSafeRe ρ m k|)
            + |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m|) := by
            exact
              finset_sum_const_mul_add_const_mul_eq_mul_sum_add
                (Finset.range (m + 1))
                η
                (fun k =>
                  |Complex.rightSemicircleStaircaseSafeRe ρ m k -
                    Complex.rightSemicircleStaircasePrevSafeRe ρ m k|)
                |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m|
  have hvar :
      (∑ k in Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseSafeRe ρ m k -
            Complex.rightSemicircleStaircasePrevSafeRe ρ m k|)
        + |0 - Complex.rightSemicircleStaircaseSafeRe ρ m m|
        ≤ 2 * ρ :=
    Complex.sum_rightSemicircleStaircase_horizontal_connector_lengths_le
      hρ.le m
  rw [hdecomp]
  exact le_trans hnorm (mul_le_mul_of_nonneg_left hvar hη_nonneg)

/-- The horizontal connector integrals differ from their graph-point finite
difference samples by an error tending to zero. -/
theorem Complex.rightSemicircleStaircaseHorizontalIntegral_sub_sampleSum_tendsto_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        ((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htwoρ_pos : 0 < 2 * ρ :=
    real_two_mul_pos_of_pos hρ
  let η : ℝ := ε / (2 * ρ)
  have hη_pos : 0 < η := div_pos hε htwoρ_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hevent :
      ∀ᶠ m : ℕ in atTop,
        (∀ k ∈ Finset.range (m + 1),
          ∀ x ∈
            [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
              Complex.rightSemicircleStaircaseSafeRe ρ m k]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I *
                    (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ
                  (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ η) ∧
        (∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ η) :=
    Complex.rightSemicircleHorizontalIntegrand_uniform_approx_sample
      f c hρ hcont η hη_pos
  filter_upwards [hevent] with m hm
  have hbound :
      ‖((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m‖
        ≤ η * (2 * ρ) :=
    Complex.norm_sum_rightSemicircleStaircaseHorizontal_sub_sampleSum_le
      f c hρ hcont m hη_nonneg hm
  have hη_eq : η * (2 * ρ) = ε := by
    dsimp [η]
    exact div_mul_cancel_of_pos_right htwoρ_pos
  exact lt_of_le_of_lt hbound (by rw [hη_eq])

/-- Finite owner estimate for the direct path-approximation theorem.

If every point of every exterior staircase connector is `η`-close in integrand
value to the matching point of the circular graph, and if the staircase height
mesh is also controlled at scale `η`, then the whole staircase line integral
differs from the circular line integral by a bounded-variation error.

This is the finite epsilon estimate behind the standard polygonal
path-integration proof.  The later convergence theorem supplies the hypotheses
by compact uniform continuity and mesh convergence. -/
theorem Complex.norm_rightSemicircleStaircaseArcIntegral_sub_angleIntegral_le_pathApprox
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ)
    {η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (hhorizontal :
      (∀ k ∈ Finset.range (m + 1),
        ∀ x ∈
          [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
            Complex.rightSemicircleStaircaseSafeRe ρ m k]],
          ‖f ((((c.re + x : ℝ) : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
            f (Complex.rightSemicircleGraphPoint c ρ
                (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ η) ∧
      (∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
          ‖f ((((c.re + x : ℝ) : ℂ) +
                Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
            f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ η))
    (hvertical :
      ∀ k ∈ Finset.range (m + 1),
        ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
          ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                Complex.I * (((c.im + y : ℝ) : ℂ))) -
            f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η)
    (hquadrature :
      ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
        Complex.rightSemicircleGraphHorizontalIntegral f c ρ‖ ≤ η * (2 * ρ)) :
    ‖Complex.rightSemicirclePolygonalArcIntegral f c ρ m -
      Complex.rightSemicircleAngleIntegral f c ρ‖ ≤ η * (6 * ρ) := by
  have hhorizontal_bound :
      ‖((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m‖
        ≤ η * (2 * ρ) :=
    Complex.norm_sum_rightSemicircleStaircaseHorizontal_sub_sampleSum_le
      f c hρ hcont
      m hη_nonneg hhorizontal
  have hvertical_bound :
      ‖(∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
        Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
        ≤ η * (2 * ρ) :=
    Complex.norm_sum_rightSemicircleStaircaseVertical_sub_graphVertical_le
      f c hρ hcont
      m hη_nonneg hvertical
  have hangle :
      Complex.rightSemicircleAngleIntegral f c ρ =
        Complex.rightSemicircleGraphHorizontalIntegral f c ρ +
          Complex.rightSemicircleGraphVerticalIntegral f c ρ := by
    have htarget :
        Complex.rightSemicircleGraphHorizontalIntegral f c ρ +
            Complex.rightSemicircleGraphVerticalIntegral f c ρ =
          Complex.rightSemicircleAngleIntegral f c ρ := by
      dsimp [Complex.rightSemicircleGraphHorizontalIntegral]
      exact
        horizontal_add_vertical_eq_total
          (Complex.rightSemicircleAngleIntegral f c ρ)
          (Complex.rightSemicircleGraphVerticalIntegral f c ρ)
    exact htarget.symm
  have hdecomp :
      Complex.rightSemicirclePolygonalArcIntegral f c ρ m -
          Complex.rightSemicircleAngleIntegral f c ρ =
        (((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m) +
        (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
          Complex.rightSemicircleGraphHorizontalIntegral f c ρ) +
        ((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
          Complex.rightSemicircleGraphVerticalIntegral f c ρ) := by
    dsimp [Complex.rightSemicirclePolygonalArcIntegral]
    rw [hangle]
    rw [Finset.sum_add_distrib]
    exact
      polygonal_arc_error_decompose_additive
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k)
        (Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)
        (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)
        (Complex.rightSemicircleGraphVerticalIntegral f c ρ)
  rw [hdecomp]
  calc
    ‖(((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m) +
      (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
        Complex.rightSemicircleGraphHorizontalIntegral f c ρ) +
      ((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
        Complex.rightSemicircleGraphVerticalIntegral f c ρ)‖
        ≤
          ‖((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
              Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m‖ +
          ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
            Complex.rightSemicircleGraphHorizontalIntegral f c ρ‖ +
          ‖(∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
            Complex.rightSemicircleGraphVerticalIntegral f c ρ‖ := by
            exact le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
    _ ≤ η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) := by
            exact add_le_add (add_le_add hhorizontal_bound hquadrature) hvertical_bound
    _ ≤ η * (6 * ρ) := by
            exact three_two_radius_errors_le_six_radius_error hη_nonneg hρ.le

/-- Endpoint defect between the exterior safe horizontal endpoint of a
staircase cell and the right endpoint of the true circular graph over that
cell. -/
noncomputable def Complex.rightSemicircleStaircaseSafeEndpointDefect
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  Complex.rightSemicircleStaircaseSafeRe ρ m k -
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m (k + 1))

/-- Cells strictly below the midpoint have no endpoint defect: the safe
coordinate is already the right endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeEndpointDefect_eq_zero_of_lt_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k < (m + 1) / 2) :
    Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k = 0 := by
  have hk_succ_le_mid : k + 1 ≤ (m + 1) / 2 :=
    Nat.succ_le_of_lt hk
  have hy_succ_nonpos :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0 :=
    Complex.rightSemicircleStaircaseY_nonpos_of_le_midpoint
      hρ hk_succ_le_mid
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos
      hρ m k hy_succ_nonpos
  dsimp [Complex.rightSemicircleStaircaseSafeEndpointDefect]
  rw [hsafe]
  exact sub_self

/-- Every individual endpoint defect is bounded by the radius. -/
theorem Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| ≤ ρ := by
  have hsafe_mem :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ m k hk
  have hk_succ_range : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy_succ_mem :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m (k + 1) hk_succ_range
  have hgraph_mem :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleGraphRe_mem_radius_uIcc_of_height_mem hρ hy_succ_mem
  dsimp [Complex.rightSemicircleStaircaseSafeEndpointDefect]
  exact abs_sub_le_radius_of_mem_radius_uIcc hρ hsafe_mem hgraph_mem

/-- If a grid index lies strictly above the midpoint, its predecessor is at or
above the midpoint. -/
theorem Complex.midpoint_le_pred_of_midpoint_lt
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    (m + 1) / 2 ≤ k - 1 :=
  Nat.le_pred_of_lt hk

/-- A grid index strictly above the midpoint is nonzero. -/
theorem Complex.ne_zero_of_midpoint_lt
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    k ≠ 0 :=
  Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le ((m + 1) / 2)) hk)

/-- Strictly above the midpoint, the lower endpoint height is nonnegative. -/
theorem Complex.rightSemicircleStaircaseY_nonneg_of_midpoint_lt
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    0 ≤ Complex.rightSemicircleStaircaseY ρ m k := by
  have hmid_le_pred : (m + 1) / 2 ≤ k - 1 :=
    Complex.midpoint_le_pred_of_midpoint_lt hk
  have hpred_succ : (k - 1) + 1 = k :=
    Complex.staircase_pred_succ_of_ne_zero
      (Complex.ne_zero_of_midpoint_lt hk)
  simpa [hpred_succ] using
    Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
      hρ hmid_le_pred

/-- Strictly above the crossing cell, the endpoint defect is the drop of the
right semicircle graph between adjacent grid points. -/
theorem Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_eq_graph_drop_of_midpoint_lt
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 < k) :
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) -
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hy_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseY_nonneg_of_midpoint_lt hρ hk
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
      hρ m k hy_nonneg
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  have hgraph_drop :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
  have hdrop_nonneg :
      0 ≤
        Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    sub_nonneg.mpr hgraph_drop
  dsimp [Complex.rightSemicircleStaircaseSafeEndpointDefect]
  rw [hsafe]
  exact abs_of_nonneg hdrop_nonneg

/-- The suffix of endpoint defects above the crossing telescopes to at most
one radius. -/
theorem Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_suffix_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    (∑ t in Finset.range (m - (m + 1) / 2),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m
        (((m + 1) / 2) + 1 + t)|) ≤ ρ := by
  let j : ℕ := (m + 1) / 2
  let start : ℕ := j + 1
  let r : ℕ → ℝ := fun k =>
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  have hjm : j ≤ m := by
    dsimp [j]
    exact nat_staircase_midpoint_le m
  have hend_index : start + (m - j) = m + 1 := by
    dsimp [start]
    exact nat_succ_add_sub_eq_succ hjm
  have hterm :
      ∀ t ∈ Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)| =
          |r ((start + t) + 1) - r (start + t)| := by
    intro t _ht
    have hj_lt_index : j < start + t := by
      dsimp [start]
      exact nat_lt_succ_add j t
    have hdrop :
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)| =
          r (start + t) - r ((start + t) + 1) := by
      simpa [j, start, r] using
        Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_eq_graph_drop_of_midpoint_lt
          hρ (m := m) (k := start + t) hj_lt_index
    have hdrop_abs :
        |r ((start + t) + 1) - r (start + t)| =
          r (start + t) - r ((start + t) + 1) := by
      have hmid_lt_index : j < start + t := hj_lt_index
      have hindex_pos : 0 < start + t :=
        lt_of_le_of_lt (Nat.zero_le j) hmid_lt_index
      have hmid_le_pred : j ≤ start + t - 1 :=
        Nat.le_pred_of_lt hmid_lt_index
      have hpred_succ : (start + t - 1) + 1 = start + t :=
        Nat.sub_add_cancel hindex_pos
      have hy_nonneg :
          0 ≤ Complex.rightSemicircleStaircaseY ρ m (start + t) := by
        simpa [hpred_succ, j] using
          Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
            hρ hmid_le_pred
      have hy_le :
          Complex.rightSemicircleStaircaseY ρ m (start + t) ≤
            Complex.rightSemicircleStaircaseY ρ m ((start + t) + 1) :=
        Complex.rightSemicircleStaircaseY_le_succ hρ m (start + t)
      have hanti :
          r ((start + t) + 1) ≤ r (start + t) :=
        Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
      rw [abs_of_nonpos (sub_nonpos.mpr hanti)]
      exact neg_sub (r ((start + t) + 1)) (r (start + t))
    rw [hdrop, hdrop_abs]
  have hsum_eq :
      (∑ t in Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|) =
      ∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)| := by
    apply Finset.sum_congr rfl
    intro t ht
    exact hterm t ht
  have hanti :
      ∀ t : ℕ, t < m - j → r ((start + t) + 1) ≤ r (start + t) := by
    intro t _ht
    have hj_lt_index : j < start + t := by
      dsimp [start]
      exact nat_lt_succ_add j t
    have hindex_pos : 0 < start + t :=
      lt_of_le_of_lt (Nat.zero_le j) hj_lt_index
    have hmid_le_pred : j ≤ start + t - 1 :=
      Nat.le_pred_of_lt hj_lt_index
    have hpred_succ : (start + t - 1) + 1 = start + t :=
      Nat.sub_add_cancel hindex_pos
    have hy_nonneg :
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (start + t) := by
      simpa [hpred_succ, j] using
        Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
          hρ hmid_le_pred
    have hy_le :
        Complex.rightSemicircleStaircaseY ρ m (start + t) ≤
          Complex.rightSemicircleStaircaseY ρ m ((start + t) + 1) :=
      Complex.rightSemicircleStaircaseY_le_succ hρ m (start + t)
    exact Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
  have htel :
      (∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)|) =
        r start - r (start + (m - j)) :=
    sum_abs_adjacent_of_antitone_suffix r start (m - j) hanti
  have hstart_range : start ∈ Finset.range (m + 2) := by
    dsimp [start]
    simpa [Finset.mem_range] using Nat.succ_lt_succ (Nat.lt_succ_iff.mpr hjm)
  have hystart :
      Complex.rightSemicircleStaircaseY ρ m start ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m start hstart_range
  have hrstart_le : r start ≤ ρ := by
    dsimp [r]
    exact Complex.rightSemicircleGraphRe_le_radius hρ hystart
  have hrend : r (start + (m - j)) = 0 := by
    dsimp [r]
    rw [hend_index, Complex.rightSemicircleStaircaseY_last,
      Complex.rightSemicircleGraphRe_top]
  calc
    (∑ t in Finset.range (m - (m + 1) / 2),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m
        (((m + 1) / 2) + 1 + t)|)
        =
      (∑ t in Finset.range (m - j),
        |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m (start + t)|) := by
        simp [j, start, Nat.add_assoc]
    _ =
      ∑ t in Finset.range (m - j),
        |r ((start + t) + 1) - r (start + t)| := hsum_eq
    _ = r start - r (start + (m - j)) := htel
    _ ≤ ρ := by
      rw [hrend]
      rw [sub_zero]
      exact hrstart_le

/-- Graph probe on the uniform staircase height grid. -/
noncomputable def Complex.rightSemicircleGraphProbeGrid
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  f (Complex.rightSemicircleGraphPoint c ρ
      (Complex.rightSemicircleStaircaseY ρ m k))

/-- Summation-by-parts form of the safe-coordinate horizontal sample error.

The exterior safe-coordinate increment error is not estimated termwise.  The
endpoint defects telescope, leaving adjacent differences of the graph probe
weighted by the safe endpoint defects. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_eq_endpointDefectSum
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
      Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m =
        ∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) := by
  let g : ℕ → ℂ := fun k =>
    Complex.rightSemicircleGraphProbeGrid f c ρ m k
  let r : ℕ → ℝ := fun k =>
    Complex.rightSemicircleGraphRe ρ
      (Complex.rightSemicircleStaircaseY ρ m k)
  let s : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeRe ρ m k
  let e : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k
  have hprev :
      ∀ k : ℕ,
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
            r k =
          if k = 0 then
            0
          else
            e (k - 1) := by
    intro k
    by_cases hk : k = 0
    · subst k
      have hr0 : r 0 = 0 := by
        dsimp [r]
        rw [Complex.rightSemicircleStaircaseY_zero,
          Complex.rightSemicircleGraphRe_bottom]
      rw [if_pos rfl]
      dsimp [Complex.rightSemicircleStaircasePrevSafeRe]
      rw [hr0, sub_zero]
    · have hsucc : (k - 1) + 1 = k :=
        Complex.staircase_pred_succ_of_ne_zero hk
      rw [if_neg hk]
      dsimp [Complex.rightSemicircleStaircasePrevSafeRe, e,
        Complex.rightSemicircleStaircaseSafeEndpointDefect, r]
      rw [hsucc]
  have hcell :
      ∀ k ∈ Finset.range (m + 1),
        g k *
            (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
                Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) -
          g k *
            (((r (k + 1) - r k : ℝ) : ℂ)) =
        g k * ((e k : ℝ) : ℂ) -
          g k *
            (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
                r k : ℝ) : ℂ)) := by
    intro k _hk
    dsimp [e, Complex.rightSemicircleStaircaseSafeEndpointDefect]
    exact
      safe_endpoint_cell_error_algebra
        (g k)
        (Complex.rightSemicircleStaircaseSafeRe ρ m k)
        (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
        (r (k + 1))
        (r k)
  have hsum_shift :
      (∑ k in Finset.range (m + 1),
        g k *
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
              r k : ℝ) : ℂ))) =
      ∑ k in Finset.range m,
        g (k + 1) * ((e k : ℝ) : ℂ) := by
    rw [Finset.sum_range_succ']
    have hzero :
        g 0 *
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 -
              r 0 : ℝ) : ℂ)) = 0 := by
      have hprev0 := hprev 0
      rw [hprev0]
      simp
    rw [hzero, zero_add]
    apply Finset.sum_congr rfl
    intro k _hk
    have hprev_succ := hprev (k + 1)
    have hnot : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rw [hprev_succ, if_neg hnot]
    simp
  have htop :
      Complex.rightSemicircleGraphProbeGrid f c ρ m (m + 1) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)) =
        -g (m + 1) * ((e m : ℝ) : ℂ) := by
    have hrtop : r (m + 1) = 0 := by
      dsimp [r]
      rw [Complex.rightSemicircleStaircaseY_last,
        Complex.rightSemicircleGraphRe_top]
    dsimp [g, e, Complex.rightSemicircleStaircaseSafeEndpointDefect]
    rw [hrtop]
    exact
      top_connector_scalar_eq_neg_endpoint_defect_scalar
        (f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m (m + 1))))
        (Complex.rightSemicircleStaircaseSafeRe ρ m m)
  dsimp [Complex.rightSemicircleStaircaseHorizontalSampleSum,
    Complex.rightSemicircleGraphHorizontalSampleSum,
    Complex.rightSemicircleGraphProbeGrid, g, r] at hcell hsum_shift htop ⊢
  calc
    (∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) +
        f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))) -
      ∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))
        =
      (∑ k in Finset.range (m + 1),
        (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
              Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)) -
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ)))) +
        f (Complex.rightSemicircleGraphPoint c ρ ρ) *
          (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)) := by
          exact
            finset_sum_add_tail_sub_sum_eq_sum_sub_add_tail
              (Finset.range (m + 1))
              (fun k =>
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)) *
                  (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
                      Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ)))
              (fun k =>
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m k)) *
                  (((Complex.rightSemicircleGraphRe ρ
                        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
                      Complex.rightSemicircleGraphRe ρ
                        (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ)))
              (f (Complex.rightSemicircleGraphPoint c ρ ρ) *
                (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ)))
    _ =
      (∑ k in Finset.range (m + 1),
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) -
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)) *
          (((Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))) -
        f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m (m + 1))) *
          ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m m : ℝ) : ℂ) := by
          apply congrArg₂ HAdd.hAdd
          · apply Finset.sum_congr rfl
            intro k hk
            exact hcell k hk
          · have hpoint :
              f (Complex.rightSemicircleGraphPoint c ρ ρ) =
                f (Complex.rightSemicircleGraphPoint c ρ
                    (Complex.rightSemicircleStaircaseY ρ m (m + 1))) := by
                rw [Complex.rightSemicircleStaircaseY_last]
            rw [hpoint]
            exact htop
    _ =
      ∑ k in Finset.range (m + 1),
          (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
            Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
            ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ) := by
          dsimp [Complex.rightSemicircleGraphProbeGrid]
          rw [Finset.sum_sub_distrib, hsum_shift]
          exact
            endpoint_defect_summation_by_parts_algebra
              m
              (fun k =>
                f (Complex.rightSemicircleGraphPoint c ρ
                  (Complex.rightSemicircleStaircaseY ρ m k)))
              (fun k =>
                ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ))

/-- The total safe endpoint defect is uniformly bounded by twice the radius.

The lower-half cells have zero defect, the upper-half cells telescope against
the decreasing circular graph, and the single crossing cell is bounded by the
radius. -/
theorem Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_le_two_radius
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
        ≤ 2 * ρ := by
  let j : ℕ := (m + 1) / 2
  let e : ℕ → ℝ := fun k =>
    |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|
  have hjm : j ≤ m := by
    dsimp [j]
    exact nat_staircase_midpoint_le m
  have hlen : j + (1 + (m - j)) = m + 1 := by
    calc
      j + (1 + (m - j)) = j + 1 + (m - j) := by
        exact (Nat.add_assoc j 1 (m - j)).symm
      _ = m + 1 := nat_succ_add_sub_eq_succ hjm
  have hsplit :
      (∑ k in Finset.range (m + 1), e k) =
        (∑ k in Finset.range j, e k) + e j +
          ∑ t in Finset.range (m - j), e (j + 1 + t) := by
    calc
      (∑ k in Finset.range (m + 1), e k)
          =
        ∑ k in Finset.range (j + (1 + (m - j))), e k := by
          rw [hlen]
      _ =
        (∑ k in Finset.range j, e k) +
          ∑ t in Finset.range (1 + (m - j)), e (j + t) := by
          rw [Finset.sum_range_add]
      _ =
        (∑ k in Finset.range j, e k) +
          (e j + ∑ t in Finset.range (m - j), e (j + 1 + t)) := by
          rw [nat_one_add_eq_add_one (m - j)]
          rw [Finset.sum_range_succ']
          apply congrArg₂ HAdd.hAdd rfl
          apply congrArg₂ HAdd.hAdd
          · simp
          · apply Finset.sum_congr rfl
            intro t _ht
            have hidx : j + (t + 1) = j + 1 + t := by
              exact nat_midpoint_suffix_index_assoc j t
            rw [hidx]
      _ =
        (∑ k in Finset.range j, e k) + e j +
          ∑ t in Finset.range (m - j), e (j + 1 + t) := by
          exact
            (add_assoc
              (∑ k in Finset.range j, e k)
              (e j)
              (∑ t in Finset.range (m - j), e (j + 1 + t))).symm
  have hlower :
      (∑ k in Finset.range j, e k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk_lt : k < j := by
      simpa [Finset.mem_range] using hk
    have hzero :
        Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k = 0 :=
      Complex.rightSemicircleStaircaseSafeEndpointDefect_eq_zero_of_lt_midpoint
        hρ.le (m := m) (k := k) (by simpa [j] using hk_lt)
    dsimp [e]
    rw [hzero, abs_zero]
  have hj_range : j ∈ Finset.range (m + 1) := by
    simpa [Finset.mem_range] using Nat.lt_succ_iff.mpr hjm
  have hcross : e j ≤ ρ := by
    dsimp [e]
    exact
      Complex.abs_rightSemicircleStaircaseSafeEndpointDefect_le_radius
        hρ.le m j hj_range
  have hsuffix :
      (∑ t in Finset.range (m - j), e (j + 1 + t)) ≤ ρ := by
    dsimp [e, j]
    exact
      Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_suffix_le_radius
        hρ.le m
  calc
    (∑ k in Finset.range (m + 1),
      |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
        =
      ∑ k in Finset.range (m + 1), e k := by
        simp [e]
    _ =
      (∑ k in Finset.range j, e k) + e j +
        ∑ t in Finset.range (m - j), e (j + 1 + t) := hsplit
    _ ≤ 2 * ρ := by
      rw [hlower]
      rw [zero_add]
      exact add_le_two_mul_of_each_le hcross hsuffix

/-- Adjacent graph probes on the staircase height grid become uniformly
close. -/
theorem Complex.rightSemicircleGraphProbeGrid_adjacent_uniform_tendsto_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
          (fun k =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖))
      atTop
      (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hprobe_cont :
      ContinuousOn
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
      f c hρ hcont
  have hprobe_uniform :
      UniformContinuousOn
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
        (Set.Icc (-ρ) ρ) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hprobe_cont
  rcases (Metric.uniformContinuousOn_iff.mp hprobe_uniform ε hε) with
    ⟨δ, hδ, hδ_modulus⟩
  have hmesh :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| < δ :=
    Complex.eventually_rightSemicircleStaircase_cell_length_lt hρ hδ
  filter_upwards [hmesh] with m hm
  rw [dist_eq_norm]
  exact Finset.sup'_lt_iff.mpr
    (by
      intro k hk
      have hk0 : k ∈ Finset.range (m + 2) := by
        exact Complex.staircase_lower_sample_mem_range hk
      have hk1 : k + 1 ∈ Finset.range (m + 2) := by
        exact Complex.staircase_upper_sample_mem_range hk
      have hy0 :
          Complex.rightSemicircleStaircaseY ρ m k ∈ Set.Icc (-ρ) ρ := by
        exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ.le
          (Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0)
      have hy1 :
          Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ Set.Icc (-ρ) ρ := by
        exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ.le
          (Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1)
      have hdist :
          dist
            (Complex.rightSemicircleStaircaseY ρ m k)
            (Complex.rightSemicircleStaircaseY ρ m (k + 1)) < δ := by
        dsimp [dist]
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hm k hk
      have hclose :
          dist
            (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k)))
            (f (Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)))) < ε :=
        hδ_modulus
          (Complex.rightSemicircleStaircaseY ρ m k) hy0
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) hy1
          hdist
      dsimp [Complex.rightSemicircleGraphProbeGrid]
      simpa [dist_eq_norm] using hclose)

/-- Endpoint-defect summation-by-parts estimate for the safe-coordinate
horizontal sample error. -/
theorem Complex.norm_rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_le_endpointDefect
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m : ℕ) :
    ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
      Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m‖
      ≤
        (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
          (fun k =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
        (2 * ρ) := by
  rw [Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_eq_endpointDefectSum]
  calc
    ‖∑ k in Finset.range (m + 1),
        (Complex.rightSemicircleGraphProbeGrid f c ρ m k -
          Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
          ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖
        ≤
      ∑ k in Finset.range (m + 1),
        ‖(Complex.rightSemicircleGraphProbeGrid f c ρ m k -
          Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)) *
          ((Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k : ℝ) : ℂ)‖ :=
          Finset.norm_sum_le _ _
    _ ≤
      ∑ k in Finset.range (m + 1),
        (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
          (fun j =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m j -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (j + 1)‖)) *
          |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul, Complex.norm_ofReal, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right
            (Finset.le_sup' (Finset.range (m + 1)) _ k hk)
            (abs_nonneg _)
    _ =
      (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
          (fun j =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m j -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (j + 1)‖)) *
        ∑ k in Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k| := by
          exact
            finset_sum_const_mul_eq_mul_sum
              (Finset.range (m + 1))
              (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
                (fun j =>
                  ‖Complex.rightSemicircleGraphProbeGrid f c ρ m j -
                    Complex.rightSemicircleGraphProbeGrid f c ρ m (j + 1)‖))
              (fun k =>
                |Complex.rightSemicircleStaircaseSafeEndpointDefect ρ m k|)
    _ ≤
      (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
          (fun j =>
            ‖Complex.rightSemicircleGraphProbeGrid f c ρ m j -
              Complex.rightSemicircleGraphProbeGrid f c ρ m (j + 1)‖)) *
        (2 * ρ) := by
          exact mul_le_mul_of_nonneg_left
            (Complex.sum_abs_rightSemicircleStaircaseSafeEndpointDefect_le_two_radius
              hρ m)
            (Finset.sup'_nonneg _ _ (fun k => norm_nonneg _))

/-- The safe-staircase horizontal finite-difference samples and the exact
graph-coordinate finite-difference samples have the same limit.

This is the exterior-safe coordinate half of the horizontal quadrature
argument: uniform convergence of the safe and previous-safe real coordinates
to the graph coordinate, together with a compact bound for the graph probe,
makes the weighted coordinate-increment error tend to zero. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_tendsto_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 0) := by
  have hsup :
      Tendsto
        (fun m : ℕ =>
          Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
            (fun k =>
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖))
        atTop
        (𝓝 0) :=
    Complex.rightSemicircleGraphProbeGrid_adjacent_uniform_tendsto_zero
      f c hρ hcont
  have hprod :
      Tendsto
        (fun m : ℕ =>
          (Finset.sup' (Finset.range (m + 1)) ⟨0, by simp⟩
            (fun k =>
              ‖Complex.rightSemicircleGraphProbeGrid f c ρ m k -
                Complex.rightSemicircleGraphProbeGrid f c ρ m (k + 1)‖)) *
            (2 * ρ))
        atTop
        (𝓝 (0 * (2 * ρ))) :=
    hsup.mul tendsto_const_nhds
  exact tendsto_of_norm_tendsto_zero
    (by
      simpa using hprod)
    (fun m =>
      Complex.norm_rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_le_endpointDefect
        f c hρ hcont m)

/-- Finite Stieltjes-error estimate for the angle-grid chord sum.

The chord increment is first rewritten as the integral of `-ρ sin θ` on the
cell.  The difference from the true integral is then bounded by uniform
oscillation of the probe on each angle cell times the elementary bound
`|ρ sin θ| ≤ ρ`. -/
theorem Complex.norm_rightSemicircleAngleChordSum_sub_angleIntegral_le
    (F : ℝ → ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hF :
      ContinuousOn F
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)))
    (m : ℕ)
    {η : ℝ}
    (hη_nonneg : 0 ≤ η)
    (happrox :
      ∀ k ∈ Finset.range (m + 1),
        ∀ θ ∈
          [[Complex.rightSemicircleAngleGrid ρ m k,
            Complex.rightSemicircleAngleGrid ρ m (k + 1)]],
          ‖F (Complex.rightSemicircleAngleGrid ρ m k) - F θ‖ ≤ η) :
    ‖(∑ k in Finset.range (m + 1),
        F (Complex.rightSemicircleAngleGrid ρ m k) *
          (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
             ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ))) -
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))‖
      ≤ η * (Real.pi * ρ) := by
  let a : ℕ → ℝ := fun k => Complex.rightSemicircleAngleGrid ρ m k
  let D : ℝ → ℂ := fun θ => (((-ρ * Real.sin θ : ℝ) : ℂ))
  let G : ℝ → ℂ := fun θ => F θ * D θ
  have hA : a 0 = -(Real.pi / 2) := by
    dsimp [a]
    exact Complex.rightSemicircleAngleGrid_zero hρ m
  have hB : a (m + 1) = Real.pi / 2 := by
    dsimp [a]
    exact Complex.rightSemicircleAngleGrid_last hρ m
  have hD_cont : Continuous D := by
    dsimp [D]
    exact continuous_ofReal.comp ((continuous_const.mul continuous_sin).neg)
  have hint :
      ∀ k < m + 1, IntervalIntegrable G volume (a k) (a (k + 1)) := by
    intro k hk
    have hkmem : k ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range] using hk
    have hsubset :
        [[a k, a (k + 1)]] ⊆
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      dsimp [a]
      exact Complex.rightSemicircleAngleGrid_cell_subset_Icc hρ hkmem
    have hFcell : ContinuousOn F [[a k, a (k + 1)]] :=
      hF.mono hsubset
    have hDcell : ContinuousOn D [[a k, a (k + 1)]] :=
      hD_cont.continuousOn
    exact (hFcell.mul hDcell).intervalIntegrable
  have hintegral_split :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G θ) =
        ∑ k in Finset.range (m + 1),
          ∫ θ : ℝ in a k..a (k + 1), G θ := by
    exact
      Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
        G a (m + 1) (-(Real.pi / 2)) (Real.pi / 2)
        hA hB hint
  have hterm :
      ∀ k ∈ Finset.range (m + 1),
        F (a k) *
            (((ρ * Real.cos (a (k + 1)) -
               ρ * Real.cos (a k) : ℝ) : ℂ)) -
          ∫ θ : ℝ in a k..a (k + 1), G θ =
        ∫ θ : ℝ in a k..a (k + 1),
          (F (a k) - F θ) * D θ := by
    intro k hk
    have hconst :
        IntervalIntegrable (fun θ : ℝ => F (a k) * D θ)
          volume (a k) (a (k + 1)) := by
      exact (hD_cont.continuousOn.const_mul (F (a k))).intervalIntegrable
    have hGcell :
        IntervalIntegrable G volume (a k) (a (k + 1)) := by
      exact hint k (Complex.staircase_cell_index_lt hk)
    have hchord :
        (((ρ * Real.cos (a (k + 1)) -
           ρ * Real.cos (a k) : ℝ) : ℂ)) =
          ∫ θ : ℝ in a k..a (k + 1), D θ := by
      dsimp [a, D]
      have hreal :=
        Complex.rightSemicircleAngleGrid_cos_chord_eq_integral_dx
          (ρ := ρ) m k
      calc
        (((ρ * Real.cos (a (k + 1)) -
           ρ * Real.cos (a k) : ℝ) : ℂ)) =
            ((∫ θ : ℝ in a k..a (k + 1), -ρ * Real.sin θ : ℝ) : ℂ) := by
          exact congrArg (fun x : ℝ => (x : ℂ)) hreal
        _ =
            ∫ θ : ℝ in a k..a (k + 1), ((-ρ * Real.sin θ : ℝ) : ℂ) := by
          exact (RCLike.intervalIntegral_ofReal (𝕜 := ℂ)).symm
    calc
      F (a k) *
            (((ρ * Real.cos (a (k + 1)) -
               ρ * Real.cos (a k) : ℝ) : ℂ)) -
          ∫ θ : ℝ in a k..a (k + 1), G θ
          =
        (∫ θ : ℝ in a k..a (k + 1), F (a k) * D θ) -
          ∫ θ : ℝ in a k..a (k + 1), G θ := by
            rw [hchord]
            rw [intervalIntegral.integral_const_mul]
      _ =
        ∫ θ : ℝ in a k..a (k + 1),
          (F (a k) * D θ - G θ) := by
            rw [intervalIntegral.integral_sub hconst hGcell]
      _ =
        ∫ θ : ℝ in a k..a (k + 1),
          (F (a k) - F θ) * D θ := by
            apply intervalIntegral.integral_congr
            intro θ _hθ
            dsimp [G]
            exact
              rightSemicircleAngle_dx_cell_integrand_error_factor
                (F (a k))
                (F θ)
                (D θ)
  have hcell_bound :
      ∀ k ∈ Finset.range (m + 1),
        ‖F (a k) *
              (((ρ * Real.cos (a (k + 1)) -
                 ρ * Real.cos (a k) : ℝ) : ℂ)) -
            ∫ θ : ℝ in a k..a (k + 1), G θ‖
          ≤ η * ρ * |a (k + 1) - a k| := by
    intro k hk
    rw [hterm k hk]
    have hle :
        ∀ θ ∈ Set.uIoc (a k) (a (k + 1)),
          ‖(F (a k) - F θ) * D θ‖ ≤ η * ρ := by
      intro θ hθ
      have hθcell : θ ∈ [[a k, a (k + 1)]] :=
        Set.uIoc_subset_uIcc hθ
      have hosc : ‖F (a k) - F θ‖ ≤ η := by
        dsimp [a] at hθcell
        exact happrox k hk θ hθcell
      have hD : ‖D θ‖ ≤ ρ := by
        dsimp [D]
        rw [Complex.norm_ofReal, Real.norm_eq_abs]
        calc
          | -ρ * Real.sin θ | = ρ * |Real.sin θ| := by
            rw [abs_mul, abs_neg, abs_of_nonneg hρ.le]
          _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hρ.le
          _ = ρ := mul_one ρ
      calc
        ‖(F (a k) - F θ) * D θ‖
            = ‖F (a k) - F θ‖ * ‖D θ‖ := norm_mul _ _
        _ ≤ η * ρ := mul_le_mul hosc hD (norm_nonneg _) hη_nonneg
    exact intervalIntegral.norm_integral_le_of_norm_le_const hle
  have hdecomp :
      (∑ k in Finset.range (m + 1),
        F (a k) *
          (((ρ * Real.cos (a (k + 1)) -
             ρ * Real.cos (a k) : ℝ) : ℂ))) -
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), G θ) =
        ∑ k in Finset.range (m + 1),
          (F (a k) *
              (((ρ * Real.cos (a (k + 1)) -
                 ρ * Real.cos (a k) : ℝ) : ℂ)) -
            ∫ θ : ℝ in a k..a (k + 1), G θ) := by
    rw [hintegral_split]
    exact Finset.sum_sub_distrib.symm
  have hsum_lengths :
      (∑ k in Finset.range (m + 1), |a (k + 1) - a k|) = Real.pi := by
    have hmono : ∀ k < m + 1, a k ≤ a (k + 1) := by
      intro k hk
      dsimp [a]
      exact Complex.rightSemicircleAngleGrid_monotone hρ m k hk
    have htel :
        (∑ k in Finset.range (m + 1), |a (k + 1) - a k|) =
          a (m + 1) - a 0 := by
      have habs :
          ∀ k ∈ Finset.range (m + 1),
            |a (k + 1) - a k| = a (k + 1) - a k := by
        intro k hk
        exact abs_of_nonneg
          (sub_nonneg.mpr (hmono k (Complex.staircase_cell_index_lt hk)))
      simp_rw [habs]
      exact Finset.sum_range_sub' a (m + 1)
    rw [htel, hA, hB]
    exact pi_div_two_sub_neg_pi_div_two
  dsimp [a, D, G] at hdecomp ⊢
  rw [hdecomp]
  calc
    ‖∑ k in Finset.range (m + 1),
        (F (Complex.rightSemicircleAngleGrid ρ m k) *
            (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
               ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)) -
          ∫ θ : ℝ in
            Complex.rightSemicircleAngleGrid ρ m k..
              Complex.rightSemicircleAngleGrid ρ m (k + 1),
            F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))‖
        ≤
          ∑ k in Finset.range (m + 1),
            ‖F (Complex.rightSemicircleAngleGrid ρ m k) *
                (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
                   ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)) -
              ∫ θ : ℝ in
                Complex.rightSemicircleAngleGrid ρ m k..
                  Complex.rightSemicircleAngleGrid ρ m (k + 1),
                F θ * (((-ρ * Real.sin θ : ℝ) : ℂ))‖ := by
          exact Finset.norm_sum_le _ _
    _ ≤
          ∑ k in Finset.range (m + 1),
            η * ρ *
              |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                Complex.rightSemicircleAngleGrid ρ m k| := by
          dsimp [a, D, G] at hcell_bound
          exact Finset.sum_le_sum hcell_bound
    _ =
          η * ρ *
            ∑ k in Finset.range (m + 1),
              |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                Complex.rightSemicircleAngleGrid ρ m k| := by
          exact
            finset_sum_two_const_mul_eq_mul_mul_sum
              (Finset.range (m + 1))
              η
              ρ
              (fun k =>
                |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                  Complex.rightSemicircleAngleGrid ρ m k|)
    _ = η * ρ * Real.pi := by
          dsimp [a] at hsum_lengths
          rw [hsum_lengths]
    _ = η * (Real.pi * ρ) := by
          exact eta_mul_radius_mul_pi_eq_eta_mul_pi_mul_radius η ρ

/-- Angle-grid chord sums converge to the `dx` integral of the right
semicircle. -/
theorem Complex.rightSemicircleAngleChordSum_tendsto_angle_dx
    (F : ℝ → ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hF :
      ContinuousOn F
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))) :
    Tendsto
      (fun m : ℕ =>
        ∑ k in Finset.range (m + 1),
          F (Complex.rightSemicircleAngleGrid ρ m k) *
            (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
               ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)))
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hπρ_pos : 0 < Real.pi * ρ := mul_pos Real.pi_pos hρ
  let η : ℝ := ε / (Real.pi * ρ)
  have hη_pos : 0 < η := div_pos hε hπρ_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hF_uniform :
      UniformContinuousOn F
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF
  rcases (Metric.uniformContinuousOn_iff.mp hF_uniform η hη_pos) with
    ⟨δ, hδ, hδ_modulus⟩
  have hmesh :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
            Complex.rightSemicircleAngleGrid ρ m k| < δ :=
    Complex.eventually_rightSemicircleAngleGrid_cell_length_lt hρ hδ
  filter_upwards [hmesh] with m hm
  have happrox :
      ∀ k ∈ Finset.range (m + 1),
        ∀ θ ∈
          [[Complex.rightSemicircleAngleGrid ρ m k,
            Complex.rightSemicircleAngleGrid ρ m (k + 1)]],
          ‖F (Complex.rightSemicircleAngleGrid ρ m k) - F θ‖ ≤ η := by
    intro k hk θ hθ
    have hendpoints :=
      Complex.rightSemicircleAngleGrid_cell_endpoints_mem_Icc hρ hk
    have hθ_Icc :
        θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      Complex.rightSemicircleAngleGrid_cell_subset_Icc hρ hk hθ
    have htag_Icc :
        Complex.rightSemicircleAngleGrid ρ m k ∈
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
      hendpoints.1
    have hcell :
        (Complex.rightSemicircleAngleGrid ρ m k ≤ θ ∧
            θ ≤ Complex.rightSemicircleAngleGrid ρ m (k + 1)) ∨
          (Complex.rightSemicircleAngleGrid ρ m (k + 1) ≤ θ ∧
            θ ≤ Complex.rightSemicircleAngleGrid ρ m k) := by
      simpa [Set.mem_uIcc] using hθ
    have hdist_grid :
        dist θ (Complex.rightSemicircleAngleGrid ρ m k) <
          δ := by
      dsimp [dist]
      rw [Real.norm_eq_abs]
      rcases hcell with hcell | hcell
      · have hnonneg :
            0 ≤ θ - Complex.rightSemicircleAngleGrid ρ m k := by
          exact sub_nonneg.mpr hcell.1
        have hle :
            θ - Complex.rightSemicircleAngleGrid ρ m k ≤
              Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                Complex.rightSemicircleAngleGrid ρ m k := by
          exact sub_le_sub_right hcell.2 _
        have hgrid_abs :
            |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
              Complex.rightSemicircleAngleGrid ρ m k| =
              Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                Complex.rightSemicircleAngleGrid ρ m k := by
          exact abs_of_nonneg
            (sub_nonneg.mpr
              (Complex.rightSemicircleAngleGrid_monotone hρ m k
                (by simpa [Finset.mem_range] using hk)))
        rw [abs_of_nonneg hnonneg]
        exact lt_of_le_of_lt hle (by rw [← hgrid_abs]; exact hm k hk)
      · have hnonneg :
            0 ≤ Complex.rightSemicircleAngleGrid ρ m k - θ := by
          exact sub_nonneg.mpr hcell.2
        have hle :
            Complex.rightSemicircleAngleGrid ρ m k - θ ≤
              Complex.rightSemicircleAngleGrid ρ m k -
                Complex.rightSemicircleAngleGrid ρ m (k + 1) := by
          exact sub_le_sub_left hcell.1 _
        have hreverse_nonpos :
            Complex.rightSemicircleAngleGrid ρ m k -
                Complex.rightSemicircleAngleGrid ρ m (k + 1) ≤ 0 := by
          exact sub_nonpos.mpr
            (Complex.rightSemicircleAngleGrid_monotone hρ m k
              (by simpa [Finset.mem_range] using hk))
        have hzero :
            Complex.rightSemicircleAngleGrid ρ m k - θ = 0 := by
          exact le_antisymm (le_trans hle hreverse_nonpos) hnonneg
        rw [abs_of_nonneg hnonneg, hzero]
        exact hδ
    have hclose : dist (F θ) (F (Complex.rightSemicircleAngleGrid ρ m k)) < η :=
      hδ_modulus θ hθ_Icc
        (Complex.rightSemicircleAngleGrid ρ m k) htag_Icc
        hdist_grid
    have hnorm :
        ‖F θ - F (Complex.rightSemicircleAngleGrid ρ m k)‖ < η := by
      simpa [dist_eq_norm] using hclose
    have hnorm_symm :
        ‖F (Complex.rightSemicircleAngleGrid ρ m k) - F θ‖ < η := by
      simpa [norm_neg, sub_eq_add_neg, add_comm] using hnorm
    exact le_of_lt hnorm_symm
  have hbound :
      ‖(∑ k in Finset.range (m + 1),
          F (Complex.rightSemicircleAngleGrid ρ m k) *
            (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
               ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ))) -
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))‖
        ≤ η * (Real.pi * ρ) :=
    Complex.norm_rightSemicircleAngleChordSum_sub_angleIntegral_le
      F hρ hF m hη_nonneg happrox
  have hη_eq : η * (Real.pi * ρ) = ε := by
    dsimp [η]
    exact div_mul_cancel_of_pos_right hπρ_pos
  exact lt_of_le_of_lt hbound (by rw [hη_eq])

/-- Exact graph-coordinate finite-difference samples converge to the horizontal
`dx` component of the circular graph integral.

This is the graph-coordinate Riemann-Stieltjes/chord-chain half of the
horizontal quadrature argument, for the uniform height partition and left
endpoint tags on the right semicircle graph. -/
theorem Complex.rightSemicircleGraphHorizontalSampleSum_tendsto_graphHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  let F : ℝ → ℂ := fun θ =>
    f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
  have hF :
      ContinuousOn F
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    Complex.continuousOn_rightSemicircleAngleProbe f c hρ hcont
  have hchord :
      Tendsto
        (fun m : ℕ =>
          ∑ k in Finset.range (m + 1),
            F (Complex.rightSemicircleAngleGrid ρ m k) *
              (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
                 ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)))
        atTop
        (𝓝
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))) :=
    Complex.rightSemicircleAngleChordSum_tendsto_angle_dx F hρ hF
  have hsample :
      (fun m : ℕ =>
        Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m) =
      (fun m : ℕ =>
        ∑ k in Finset.range (m + 1),
          F (Complex.rightSemicircleAngleGrid ρ m k) *
            (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
               ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ))) := by
    funext m
    exact
      Complex.rightSemicircleGraphHorizontalSampleSum_eq_angleChordSum
        f c hρ m
  have htarget :
      Complex.rightSemicircleGraphHorizontalIntegral f c ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)) :=
    Complex.rightSemicircleGraphHorizontalIntegral_eq_angle_dx
      f c hρ hcont
  rw [hsample, htarget]
  exact hchord

/-- Owner horizontal quadrature theorem for the right semicircle staircase.

This is the only Stieltjes/chord-chain input needed by the path approximation:
the exterior-safe horizontal graph-point samples converge to the horizontal
`dx` component of the circular graph. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal_ownerQuadrature
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  have hgraph :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Complex.rightSemicircleGraphHorizontalSampleSum_tendsto_graphHorizontal
      f c hρ hcont
  have hsafe_error :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
            Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 0) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_sub_graphHorizontalSampleSum_tendsto_zero
      f c hρ hcont
  have hsum :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m +
            (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
              Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m))
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ + 0)) :=
    hgraph.add hsafe_error
  have hrewrite :
      (fun m : ℕ =>
        Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m +
          (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
            Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)) =
    (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m) := by
    funext m
    exact
      add_sub_right_cancel'
        (Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
        (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
  rw [hrewrite] at hsum
  simpa using hsum

/-- Direct path-integration owner theorem for exterior staircase
approximations of the right semicircle.

This is the standard polygonal-path convergence theorem for a continuous
integrand on the compact deleted collar: the exterior staircase has mesh
tending to zero, uniformly approximates the right circular arc, and has
uniformly bounded total variation.  It is the owner path-integration input from
which the horizontal and vertical component limits are recovered by projection;
the proof should not be routed through the horizontal graph-coordinate
Riemann-Stieltjes theorem. -/
theorem Complex.rightSemicircleStaircaseArcIntegral_tendsto_by_pathApproximation
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsixρ_pos : 0 < 6 * ρ :=
    real_six_mul_pos_of_pos hρ
  let η : ℝ := ε / (6 * ρ)
  have hη_pos : 0 < η := div_pos hε hsixρ_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have htwoρ_pos : 0 < 2 * ρ :=
    real_two_mul_pos_of_pos hρ
  have hquad_radius_pos : 0 < η * (2 * ρ) :=
    mul_pos hη_pos htwoρ_pos
  have hhorizontal_event :
      ∀ᶠ m : ℕ in atTop,
        (∀ k ∈ Finset.range (m + 1),
          ∀ x ∈
            [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
              Complex.rightSemicircleStaircaseSafeRe ρ m k]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I *
                    (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ
                  (Complex.rightSemicircleStaircaseY ρ m k))‖ ≤ η) ∧
        (∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
            ‖f ((((c.re + x : ℝ) : ℂ) +
                  Complex.I * (((c.im + ρ : ℝ) : ℂ)))) -
              f (Complex.rightSemicircleGraphPoint c ρ ρ)‖ ≤ η) :=
    Complex.rightSemicircleHorizontalIntegrand_uniform_approx_sample
      f c hρ hcont η hη_pos
  have hvertical_event :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                  Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
            ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                  Complex.I * (((c.im + y : ℝ) : ℂ))) -
              f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η :=
    Complex.rightSemicircleVerticalIntegrand_uniform_approx_graph
      f c hρ hcont η hη_pos
  have hquadrature_event :
      ∀ᶠ m : ℕ in atTop,
        ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
          Complex.rightSemicircleGraphHorizontalIntegral f c ρ‖ ≤
            η * (2 * ρ) := by
    have hquad :
        Tendsto
          (fun m : ℕ =>
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
          atTop
          (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
      Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal_ownerQuadrature
        f c hρ hcont
    have hmetric :=
      (Metric.tendsto_atTop.mp hquad (η * (2 * ρ)) hquad_radius_pos)
    filter_upwards [hmetric] with m hm
    simpa [dist_eq_norm] using le_of_lt hm
  filter_upwards [hhorizontal_event, hvertical_event, hquadrature_event] with
    m hhorizontal hvertical hquadrature
  have hbound :
      ‖Complex.rightSemicirclePolygonalArcIntegral f c ρ m -
        Complex.rightSemicircleAngleIntegral f c ρ‖ ≤ η * (6 * ρ) :=
    Complex.norm_rightSemicircleStaircaseArcIntegral_sub_angleIntegral_le_pathApprox
      f c hρ hcont m hη_nonneg hhorizontal hvertical hquadrature
  have hη_eq : η * (6 * ρ) = ε := by
    dsimp [η]
    exact div_mul_cancel_of_pos_right hsixρ_pos
  exact lt_of_le_of_lt hbound (by rw [hη_eq])

/-- The graph finite-difference horizontal samples converge to the nonzero
horizontal graph contribution.  The samples are taken from the uniform height
partition and use the safe-coordinate finite differences; this is the
owner-level path-projection consequence for the horizontal part of the right
semicircle. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  exact
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal_ownerQuadrature
      f c hρ hcont

/-- The graph finite-difference horizontal samples converge to the nonzero
`dx` component of the circular line integral. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_angle_dx
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)))) := by
  have hgraph :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
      f c hρ hcont
  have htarget :
      Complex.rightSemicircleGraphHorizontalIntegral f c ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)) :=
    Complex.rightSemicircleGraphHorizontalIntegral_eq_angle_dx
      f c hρ hcont
  exact htarget ▸ hgraph

/-- Horizontal staircase connectors, including the final top connector,
converge to the nonvertical `dx` part of the circular graph integral. -/
theorem Complex.rightSemicircleStaircaseHorizontalIntegral_tendsto_graphHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  have hsamples :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
      f c hρ hcont
  have herr :
      Tendsto
        (fun m : ℕ =>
          ((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 0) :=
    Complex.rightSemicircleStaircaseHorizontalIntegral_sub_sampleSum_tendsto_zero
      f c hρ hcont
  have hsum :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
            (((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
              Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
              Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m))
        atTop
        (𝓝
          (Complex.rightSemicircleGraphHorizontalIntegral f c ρ + 0)) :=
    hsamples.add herr
  have hpoint :
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
          (((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)) =
    fun m : ℕ =>
          (∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
    funext m
    exact
      add_sub_right_cancel'
        (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        ((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
  rw [hpoint] at hsum
  simpa using hsum

/-- Exterior staircase line-integral convergence for the right semicircle. -/
theorem Complex.rightSemicircleStaircaseArcIntegral_tendsto_owner
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  exact
    Complex.rightSemicircleStaircaseArcIntegral_tendsto_by_pathApproximation
      f c hρ hcont

/-- Exterior staircase approximations to the full inner right semicircle
converge to the circular line integral. -/
theorem Complex.rightSemicirclePolygonalArcIntegral_tendsto
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  exact
    Complex.rightSemicircleStaircaseArcIntegral_tendsto_owner
      f c hρ hcont

/-- The polygonal full half-collar boundary converges to the true curvilinear
semicircular-core boundary. -/
theorem Complex.tendsto_rightHalfRectangleDeletedDiskPolygonalCoreBoundary
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m)
      atTop
      (𝓝 (Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ)) := by
  have harc :
      Tendsto
        (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
        atTop
        (𝓝
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) :=
    Complex.rightSemicirclePolygonalArcIntegral_tendsto f c hρ hcont
  simpa [Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral] using
      ((tendsto_const_nhds : Tendsto
        (fun _ : ℕ =>
          (∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
            (∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
              Complex.I *
                (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                  f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))))
        atTop
        (𝓝
          ((∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
            (∫ x : ℝ in c.re..(c.re + ρ),
              f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
              Complex.I *
                (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                  f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))))))).sub harc)

/-- Cauchy-Goursat for the tangent-width semicircular half-collar.

This is the remaining local annular Cauchy-Goursat root: the tangent-width
half-rectangle with the center disk removed has boundary equal to the lower
tangent chord, the outer vertical tangent chord, the upper tangent chord with
opposite orientation, and the inner right semicircle with deleted-boundary
orientation.  It is a full half-collar theorem, not a lower/upper quarter-cap
polygonal theorem. -/
theorem Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ = 0 := by
  exact
    Complex.eq_zero_of_tendsto_identically_zero
      (fun m : ℕ =>
        Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero
          f c hρ m hcont hdiff)
      (Complex.tendsto_rightHalfRectangleDeletedDiskPolygonalCoreBoundary
        f c hρ hcont)

/-- The inner right edge of the radius-`ρ` core lies on the larger right edge
interval of radius `a`. -/
theorem Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc
    (c : ℂ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    c.re + ρ ∈ [[c.re, c.re + a]] := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have horder : c.re ≤ c.re + a := by
    exact le_add_of_nonneg_right ha
  have hleft : c.re ≤ c.re + ρ := by
    exact le_add_of_nonneg_right hρ.le
  have hright : c.re + ρ ≤ c.re + a := by
    exact add_le_add_left hρa c.re
  simpa [Set.uIcc_of_le horder] using And.intro hleft hright

/-- The larger right endpoint belongs to its own right-edge interval. -/
theorem Complex.rightHalfCore_outerReEndpoint_mem_outerRe_uIcc
    (c : ℂ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    c.re + a ∈ [[c.re, c.re + a]] := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  exact right_endpoint_mem_uIcc_of_le (le_add_of_nonneg_right ha)

/-- The smaller core real interval is contained in the larger real interval. -/
theorem Complex.rightHalfCore_re_uIcc_subset_outerRe_uIcc
    (c : ℂ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    [[c.re, c.re + ρ]] ⊆ [[c.re, c.re + a]] := by
  intro x hx
  have hcore_order : c.re ≤ c.re + ρ := by
    exact le_add_of_nonneg_right hρ.le
  have hxIcc : x ∈ Set.Icc c.re (c.re + ρ) := by
    simpa [Set.uIcc_of_le hcore_order] using hx
  have hleft : c.re ≤ x := hxIcc.1
  have hright : x ≤ c.re + a := by
    exact le_trans hxIcc.2 (add_le_add_left hρa c.re)
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have houter_order : c.re ≤ c.re + a := by
    exact le_add_of_nonneg_right ha
  simpa [Set.uIcc_of_le houter_order] using And.intro hleft hright

/-- Rectangle/annulus exhaustion for the right deleted half-rectangle collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_of_rectangleAnnulusExhaustion
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  have hcore_subset :
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
    intro z hz
    rcases hz with ⟨hbox, hnot_ball⟩
    rcases hbox with ⟨hre, him⟩
    have hre_big : z.re ∈ [[c.re, c.re + a]] := by
      exact Complex.rightHalfCore_re_uIcc_subset_outerRe_uIcc c hρa hρ hre
    exact ⟨⟨hre_big, him⟩, hnot_ball⟩
  have hcont_core :
      ContinuousOn f (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    hcont.mono hcore_subset
  have hdiff_core :
      DifferentiableOn ℂ f (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) :=
    hdiff.mono hcore_subset
  have hcore_zero :
      Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ = 0 :=
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundary_eq_zero
      f c hρ hcont_core hdiff_core
  have htail_zero :
      Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ = 0 :=
    Complex.rightHalfRectangleDeletedDiskCore_rectangularTailBoundary_eq_zero
      f c a hρa hρ hcont hdiff
  rcases
    Complex.rightHalfRectangleDeletedDiskCore_boundary_intervalIntegrable
      f c a hρa hρ hcont with
    ⟨hbottom_full, htop_full, _hvertical_full, _harc_full⟩
  have hbottom₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ) :=
    Complex.intervalIntegrable_of_mem_uIcc hbottom_full
      left_mem_uIcc
      (Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ)
  have hbottom₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a) :=
    Complex.intervalIntegrable_of_mem_uIcc hbottom_full
      (Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ)
      right_mem_uIcc
  have htop₁ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + ρ) :=
    Complex.intervalIntegrable_of_mem_uIcc htop_full
      left_mem_uIcc
      (Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ)
  have htop₂ :
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume (c.re + ρ) (c.re + a) :=
    Complex.intervalIntegrable_of_mem_uIcc htop_full
      (Complex.rightHalfCore_innerReEndpoint_mem_outerRe_uIcc c hρa hρ)
      right_mem_uIcc
  calc
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
        Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ +
          Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ :=
      Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_semicircularCore_add_rectangularTail
        f c a ρ hρa hbottom₁ hbottom₂ htop₁ htop₂
    _ = 0 := by
      rw [hcore_zero, htail_zero]

/-- Local Cauchy-Goursat theorem for a right deleted half-rectangle collar.

This is the reusable geometric theorem behind endpoint indentation.  The domain
is the right half of a rectangle with the center disk removed.  Its oriented
boundary is the lower chord, the upper chord with opposite orientation, the safe
vertical side, and the inner right semicircle with deleted-boundary orientation
subtracted.

Mathematically this is the standard deleted-collar Cauchy-Goursat argument:
the half-collar is exhausted by ordinary rectangles and an annular semicollar;
rectangle/annulus Cauchy-Goursat kills the piece boundaries, and the internal
edges cancel. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_of_collarCauchyGoursat
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  exact
    Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_of_rectangleAnnulusExhaustion
      f c a hρa hρ hcont hdiff

/-- Direct Cauchy-Goursat theorem for the right deleted half-rectangle core.

This owner theorem is intentionally only a wrapper over the geometric collar
Cauchy-Goursat theorem.  Abel-Plana-specific residue and boundary normalization
arguments consume this result later; they do not belong in the local topology
proof. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_owner
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  exact
    Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_of_collarCauchyGoursat
      f c a hρa hρ hcont hdiff

end

end LFunctions
end Boundary
