import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleVerticalPartition

/-!
# Semicircle graph approximation for finite-height Abel-Plana collars

This file owns the graph and angle parametrizations of the right semicircle,
the staircase-to-arc convergence theorem, and the resulting right-half-core
Cauchy-Goursat wrapper consumed by finite-hole boundary accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

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
  exact
    Eq.trans
      (congrArg (fun y : ℝ => y / ρ)
        (Complex.rightSemicircleStaircaseY_zero ρ m))
      (neg_div_self (ne_of_gt hρ))

/-- The angle grid starts at `-π/2`. -/
theorem Complex.rightSemicircleAngleGrid_zero
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleAngleGrid ρ m 0 = -(Real.pi / 2) := by
  show
    Real.arcsin (Complex.rightSemicircleStaircaseY ρ m 0 / ρ) =
      -(Real.pi / 2)
  exact
    Eq.trans
      (congrArg Real.arcsin
        (Complex.rightSemicircleAngleGrid_bottom_ratio hρ m))
      Real.arcsin_neg_one

/-- The top height-grid point has normalized height `1`. -/
theorem Complex.rightSemicircleAngleGrid_top_ratio
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (m + 1) / ρ = 1 := by
  exact
    Eq.trans
      (congrArg (fun y : ℝ => y / ρ)
        (Complex.rightSemicircleStaircaseY_last ρ m))
      (div_self (ne_of_gt hρ))

/-- The angle grid ends at `π/2`. -/
theorem Complex.rightSemicircleAngleGrid_last
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ) :
    Complex.rightSemicircleAngleGrid ρ m (m + 1) = Real.pi / 2 := by
  show
    Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (m + 1) / ρ) =
      Real.pi / 2
  exact
    Eq.trans
      (congrArg Real.arcsin
        (Complex.rightSemicircleAngleGrid_top_ratio hρ m))
      Real.arcsin_one

/-- Every angle-grid point lies in the right-semicircle angle interval. -/
theorem Complex.rightSemicircleAngleGrid_mem_Icc
    {ρ : ℝ}
    (hρ : 0 < ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleAngleGrid ρ m k ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  show
    Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
  exact Real.arcsin_mem_Icc _

/-- Dividing a height in `[-ρ,ρ]` by a positive radius lands in `[-1,1]`. -/
theorem div_radius_mem_unit_Icc_of_height_mem
    {ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-ρ, ρ]]) :
    -1 ≤ y / ρ ∧ y / ρ ≤ 1 := by
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    have hpair :
        (-ρ ≤ y ∧ y ≤ ρ) ∨ (ρ ≤ y ∧ y ≤ -ρ) :=
      Set.mem_uIcc.mp hy
    exact
      match hpair with
      | Or.inl hordered => hordered
      | Or.inr hreversed =>
          And.intro
            (le_trans (Complex.neg_radius_le_radius hρ.le) hreversed.1)
            (le_trans hreversed.2 (Complex.neg_radius_le_radius hρ.le))
  have hleft : -1 ≤ y / ρ := by
    have hmul : (-1 : ℝ) * ρ ≤ y := by
      calc
        (-1 : ℝ) * ρ = -ρ := neg_one_mul ρ
        _ ≤ y := hy_bounds.1
    exact (le_div_iff₀ hρ).mpr hmul
  have hright : y / ρ ≤ 1 := by
    exact (div_le_one hρ).mpr hy_bounds.2
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
  show
    ρ * Real.sin
      (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ)) =
        Complex.rightSemicircleStaircaseY ρ m k
  exact
    Eq.trans
      (congrArg (fun x : ℝ => ρ * x)
        (Real.sin_arcsin hdiv_bounds.1 hdiv_bounds.2))
      (mul_div_cancel₀ (Complex.rightSemicircleStaircaseY ρ m k)
        (ne_of_gt hρ))

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
  show
    Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ) ≤
      Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ)
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
    exact Set.mem_uIcc.mp hθ
  match hcell with
  | Or.inl hcell =>
    exact
      ⟨le_trans hendpoints.1.1 hcell.1,
        le_trans hcell.2 hendpoints.2.2⟩
  | Or.inr hcell =>
    exact
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
    Real.continuous_arcsin.continuousOn
  have harcsin_uniform :
      UniformContinuousOn Real.arcsin (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous harcsin_cont
  let ⟨η, hη, hη_modulus⟩ :=
    Metric.uniformContinuousOn_iff.mp harcsin_uniform δ hδ
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
    have hρnorm : ‖ρ‖ = ρ := by
      exact Real.norm_of_nonneg hρ.le
    have hsub :
        Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ -
          Complex.rightSemicircleStaircaseY ρ m k / ρ =
        (Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k) / ρ :=
      Eq.symm
        (sub_div
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))
          (Complex.rightSemicircleStaircaseY ρ m k)
          ρ)
    calc
      dist
          (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ)
          (Complex.rightSemicircleStaircaseY ρ m k / ρ) =
          ‖Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ -
            Complex.rightSemicircleStaircaseY ρ m k / ρ‖ :=
        dist_eq_norm
          (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ)
          (Complex.rightSemicircleStaircaseY ρ m k / ρ)
      _ =
          ‖(Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k) / ρ‖ :=
        congrArg norm hsub
      _ =
          ‖Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k‖ / ‖ρ‖ :=
        norm_div
          (Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k)
          ρ
      _ =
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| / ρ :=
        congrArg₂
          (fun a b : ℝ => a / b)
          (Real.norm_eq_abs
            (Complex.rightSemicircleStaircaseY ρ m (k + 1) -
              Complex.rightSemicircleStaircaseY ρ m k))
          hρnorm
      _ < η :=
        (div_lt_iff₀ hρ).mpr (hm k hk)
  have hclose :
      dist
        (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ))
        (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ)) < δ :=
    hη_modulus
      (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ) hx1
      (Complex.rightSemicircleStaircaseY ρ m k / ρ) hx0
      hratio
  show
    |Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ) -
      Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ)| < δ
  exact
      (Real.dist_eq
      (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m (k + 1) / ρ))
      (Real.arcsin (Complex.rightSemicircleStaircaseY ρ m k / ρ))) ▸ hclose

/-- Derivative of the radius-scaled cosine coordinate along the circle. -/
theorem Real.hasDerivAt_radius_mul_cos
    (ρ θ : ℝ) :
    HasDerivAt (fun θ : ℝ => ρ * Real.cos θ) (-ρ * Real.sin θ) θ := by
  have hraw :
      HasDerivAt (fun θ : ℝ => ρ * Real.cos θ)
        (ρ * (-Real.sin θ)) θ :=
    (Real.hasDerivAt_cos θ).const_mul ρ
  have hderiv :
      ρ * (-Real.sin θ) = -ρ * Real.sin θ := by
    calc
      ρ * (-Real.sin θ) = -(ρ * Real.sin θ) :=
        mul_neg ρ (Real.sin θ)
      _ = -ρ * Real.sin θ :=
        Eq.symm (neg_mul ρ (Real.sin θ))
  exact hderiv ▸ hraw

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
    exact Real.hasDerivAt_radius_mul_cos ρ θ
  have hint :
      IntervalIntegrable G' volume
        (Complex.rightSemicircleAngleGrid ρ m k)
        (Complex.rightSemicircleAngleGrid ρ m (k + 1)) := by
    have hG'_cont : Continuous G' :=
      continuous_const.mul Real.continuous_sin
    exact
      Continuous.intervalIntegrable
        (μ := volume)
        hG'_cont
        (Complex.rightSemicircleAngleGrid ρ m k)
        (Complex.rightSemicircleAngleGrid ρ m (k + 1))
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
          exact
            congrArg (fun x : ℝ => ρ ^ 2 - x)
              (mul_pow ρ (Real.sin θ) 2)
    _ = ρ ^ 2 * 1 - ρ ^ 2 * Real.sin θ ^ 2 := by
          exact
            congrArg (fun x : ℝ => x - ρ ^ 2 * Real.sin θ ^ 2)
              (Eq.symm (mul_one (ρ ^ 2)))
    _ = ρ ^ 2 * (1 - Real.sin θ ^ 2) := by
          exact (mul_sub (ρ ^ 2) 1 (Real.sin θ ^ 2)).symm
    _ = ρ ^ 2 * Real.cos θ ^ 2 := by
      exact congrArg (fun x : ℝ => ρ ^ 2 * x) (Eq.symm (Real.cos_sq' θ))
    _ = (ρ * Real.cos θ) ^ 2 := by
      exact Eq.symm (mul_pow ρ (Real.cos θ) 2)

/-- The sine parametrization sends the lower angle endpoint to the lower
height endpoint. -/
theorem radius_mul_sin_neg_pi_div_two
    (ρ : ℝ) :
    ρ * Real.sin (-(Real.pi / 2)) = -ρ := by
  calc
    ρ * Real.sin (-(Real.pi / 2))
        = ρ * (-(Real.sin (Real.pi / 2))) := by
          exact congrArg (fun s : ℝ => ρ * s) (Real.sin_neg (Real.pi / 2))
    _ = ρ * (-1 : ℝ) := by
          exact congrArg (fun s : ℝ => ρ * (-s)) Real.sin_pi_div_two
    _ = -ρ := mul_neg_one ρ

/-- The sine parametrization sends the upper angle endpoint to the upper
height endpoint. -/
theorem radius_mul_sin_pi_div_two
    (ρ : ℝ) :
    ρ * Real.sin (Real.pi / 2) = ρ := by
  calc
    ρ * Real.sin (Real.pi / 2) = ρ * (1 : ℝ) := by
      exact congrArg (fun s : ℝ => ρ * s) Real.sin_pi_div_two
    _ = ρ := mul_one ρ

/-- Multiplying the sine component of a circular tangent by `I²` gives the
negative horizontal component. -/
theorem Complex.I_real_mul_real_mul_I_eq_neg_real_mul
    (ρ s : ℝ) :
    (Complex.I * (ρ : ℂ)) * ((s : ℂ) * Complex.I) =
      ((-ρ * s : ℝ) : ℂ) := by
  calc
    (Complex.I * (ρ : ℂ)) * ((s : ℂ) * Complex.I)
        = ((Complex.I * (ρ : ℂ)) * (s : ℂ)) * Complex.I := by
      exact Eq.symm (mul_assoc (Complex.I * (ρ : ℂ)) (s : ℂ) Complex.I)
    _ = (Complex.I * ((ρ : ℂ) * (s : ℂ))) * Complex.I := by
      exact congrArg (fun z : ℂ => z * Complex.I)
        (mul_assoc Complex.I (ρ : ℂ) (s : ℂ))
    _ = Complex.I * (((ρ : ℂ) * (s : ℂ)) * Complex.I) := by
      exact mul_assoc Complex.I ((ρ : ℂ) * (s : ℂ)) Complex.I
    _ = Complex.I * (Complex.I * ((ρ : ℂ) * (s : ℂ))) := by
      exact congrArg (fun z : ℂ => Complex.I * z)
        (mul_comm ((ρ : ℂ) * (s : ℂ)) Complex.I)
    _ = (Complex.I * Complex.I) * ((ρ : ℂ) * (s : ℂ)) := by
      exact Eq.symm (mul_assoc Complex.I Complex.I ((ρ : ℂ) * (s : ℂ)))
    _ = (-1 : ℂ) * ((ρ : ℂ) * (s : ℂ)) := by
      exact congrArg (fun z : ℂ => z * ((ρ : ℂ) * (s : ℂ))) Complex.I_mul_I
    _ = -((ρ : ℂ) * (s : ℂ)) := neg_one_mul ((ρ : ℂ) * (s : ℂ))
    _ = -(((ρ * s : ℝ) : ℂ)) := by
      exact congrArg Neg.neg (Complex.ofReal_mul ρ s).symm
    _ = ((-(ρ * s) : ℝ) : ℂ) := by
      exact (Complex.ofReal_neg (ρ * s)).symm
    _ = ((-ρ * s : ℝ) : ℂ) := by
      exact congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (Eq.symm (neg_mul ρ s))

/-- The cosine component of a circular tangent is the vertical component. -/
theorem Complex.I_real_mul_real_eq_I_mul_real_mul
    (ρ c : ℝ) :
    (Complex.I * (ρ : ℂ)) * (c : ℂ) =
      Complex.I * (((ρ * c : ℝ) : ℂ)) := by
  calc
    (Complex.I * (ρ : ℂ)) * (c : ℂ)
        = Complex.I * ((ρ : ℂ) * (c : ℂ)) :=
      mul_assoc Complex.I (ρ : ℂ) (c : ℂ)
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
      Complex.I * (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      exact
        congrArg
          (fun z : ℂ => Complex.I * (ρ : ℂ) * Complex.exp z)
          (mul_comm Complex.I (θ : ℂ))
    _
        =
      Complex.I * (ρ : ℂ) *
        (((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      have hcos :
          Complex.cos (θ : ℂ) = ((Real.cos θ : ℝ) : ℂ) :=
        Eq.symm (Complex.ofReal_cos θ)
      have hsin :
          Complex.sin (θ : ℂ) = ((Real.sin θ : ℝ) : ℂ) :=
        Eq.symm (Complex.ofReal_sin θ)
      have hexp :
          Complex.exp ((θ : ℂ) * Complex.I) =
            (((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I) := by
        calc
          Complex.exp ((θ : ℂ) * Complex.I) =
              Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I :=
            Complex.exp_mul_I (θ : ℂ)
          _ = ((Real.cos θ : ℝ) : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
            exact
              congrArg
                (fun z : ℂ => z + Complex.sin (θ : ℂ) * Complex.I)
                hcos
          _ = ((Real.cos θ : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
            exact
              congrArg
                (fun z : ℂ => ((Real.cos θ : ℝ) : ℂ) + z * Complex.I)
                hsin
      exact
        congrArg
          (fun z : ℂ => Complex.I * (ρ : ℂ) * z)
          hexp
    _ =
      (Complex.I * (ρ : ℂ)) * ((Real.cos θ : ℝ) : ℂ) +
        (Complex.I * (ρ : ℂ)) * (((Real.sin θ : ℝ) : ℂ) * Complex.I) := by
      exact mul_add (Complex.I * (ρ : ℂ)) ((Real.cos θ : ℝ) : ℂ)
        (((Real.sin θ : ℝ) : ℂ) * Complex.I)
    _ =
      Complex.I * (((ρ * Real.cos θ : ℝ) : ℂ)) +
        (((-ρ * Real.sin θ : ℝ) : ℂ)) := by
      exact
        congrArg₂
          (fun x y : ℂ => x + y)
          (Complex.I_real_mul_real_eq_I_mul_real_mul ρ (Real.cos θ))
          (Complex.I_real_mul_real_mul_I_eq_neg_real_mul ρ (Real.sin θ))
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
    A * (Complex.I * B) = (A * Complex.I) * B :=
      Eq.symm (mul_assoc A Complex.I B)
    _ = (Complex.I * A) * B := by
      exact congrArg (fun z : ℂ => z * B) (mul_comm A Complex.I)
    _ = Complex.I * (A * B) := mul_assoc Complex.I A B

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
    S - V = (H + V) - V := congrArg (fun z : ℂ => z - V) hS
    _ = H := add_sub_cancel_right H V

/-- If an angle integral has named horizontal and vertical parts and the graph
vertical integral is the same vertical part, subtracting leaves the horizontal
part. -/
theorem horizontal_component_eq_of_angle_and_vertical_eq
    {A V H W : ℂ}
    (hA : A = H + W)
    (hV : V = W) :
    A - V = H := by
  exact horizontal_component_eq_of_sum_eq_add_vertical (hV.symm ▸ hA)

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

/-- A complex sample times a real interval length is the constant integral over
that interval. -/
theorem complex_sample_mul_interval_length_eq_integral_const
    (C : ℂ)
    (a b : ℝ) :
    C * (((b - a : ℝ) : ℂ)) =
      ∫ _x : ℝ in a..b, C := by
  calc
    C * (((b - a : ℝ) : ℂ)) =
        (b - a : ℝ) • C := by
          exact
            Eq.trans
              (mul_comm C (((b - a : ℝ) : ℂ)))
              rfl
    _ = ∫ _x : ℝ in a..b, C := by
          exact
            Eq.symm
              (intervalIntegral.integral_const C)

/-- Subtracting a constant sample over an interval is the integral of the
pointwise sample error. -/
theorem interval_integral_sub_const_sample_eq_integral_sub_const
    (H : ℝ → ℂ)
    (C : ℂ)
    (a b : ℝ)
    (hH : IntervalIntegrable H volume a b) :
    (∫ x : ℝ in a..b, H x) - C * (((b - a : ℝ) : ℂ)) =
      ∫ x : ℝ in a..b, H x - C := by
  calc
    (∫ x : ℝ in a..b, H x) - C * (((b - a : ℝ) : ℂ)) =
        (∫ x : ℝ in a..b, H x) - ∫ _x : ℝ in a..b, C := by
          exact
            congrArg
              (fun z : ℂ => (∫ x : ℝ in a..b, H x) - z)
              (complex_sample_mul_interval_length_eq_integral_const C a b)
    _ = ∫ x : ℝ in a..b, H x - C := by
          exact
            Eq.symm
              (intervalIntegral.integral_sub hH intervalIntegrable_const)

/-- Inserting and then cancelling a middle term decomposes a difference. -/
theorem sub_eq_sub_add_add_sub
    (A S B : ℂ) :
    A - B = (A - S) + (S - B) := by
  calc
    A - B = ((A - S) + S) - B := by
      exact congrArg (fun z : ℂ => z - B) (sub_add_cancel A S).symm
    _ = (A - S) + (S - B) := by
      exact add_sub_assoc (A - S) S B

/-- The addends `V` and `T` may be interchanged inside a left-associated
three-term sum. -/
theorem add_middle_right_comm_complex
    (H V T : ℂ) :
    (H + V) + T = (H + T) + V := by
  exact add_right_comm H V T

/-- Splitting the polygonal arc error into horizontal approximation,
horizontal quadrature, and vertical approximation errors. -/
theorem polygonal_arc_error_decompose_additive
    (H T V S GH GV : ℂ) :
    ((H + V) + T) - (GH + GV) =
      ((H + T) - S) + (S - GH) + (V - GV) := by
  calc
    ((H + V) + T) - (GH + GV)
        = ((H + T) + V) - (GH + GV) := by
          exact
            congrArg
              (fun z : ℂ => z - (GH + GV))
              (add_middle_right_comm_complex H V T)
    _ = ((H + T) - GH) + (V - GV) := by
          exact add_sub_add_comm (H + T) V GH GV
    _ = (((H + T) - S) + (S - GH)) + (V - GV) := by
          exact
            congrArg
              (fun z : ℂ => z + (V - GV))
              (sub_eq_sub_add_add_sub (H + T) S GH)

/-- Subtraction from a sum is addition of the negated subtrahend. -/
theorem sum_add_tail_sub_sum_eq_add_neg
    {ι : Type*}
    (s : Finset ι)
    (A B : ι → ℂ)
    (T : ℂ) :
    ((∑ i in s, A i) + T) - (∑ i in s, B i) =
      ((∑ i in s, A i) + T) + (-(∑ i in s, B i)) :=
  by
    let SA : ℂ := ∑ i in s, A i
    let SB : ℂ := ∑ i in s, B i
    show (SA + T) - SB = (SA + T) + (-SB)
    exact sub_eq_add_neg (SA + T) SB

/-- Subtracting a finite sum is addition of the negated finite sum. -/
theorem sum_sub_sum_eq_add_neg_sum
    {ι : Type*}
    (s : Finset ι)
    (A B : ι → ℂ) :
    (∑ i in s, A i) - (∑ i in s, B i) =
      (∑ i in s, A i) + (-(∑ i in s, B i)) :=
  by
    let SA : ℂ := ∑ i in s, A i
    let SB : ℂ := ∑ i in s, B i
    show SA - SB = SA + (-SB)
    exact sub_eq_add_neg SA SB

/-- A finite sum with a tail term minus a second finite sum splits into the
sum of pointwise differences plus the tail term. -/
theorem finset_sum_add_tail_sub_sum_eq_sum_sub_add_tail
    {ι : Type*}
    (s : Finset ι)
    (A B : ι → ℂ)
    (T : ℂ) :
    ((∑ i in s, A i) + T) - (∑ i in s, B i) =
      (∑ i in s, (A i - B i)) + T := by
  calc
    ((∑ i in s, A i) + T) - (∑ i in s, B i)
        = ((∑ i in s, A i) - (∑ i in s, B i)) + T := by
          exact
            Eq.trans
              (sum_add_tail_sub_sum_eq_add_neg s A B T)
              (Eq.trans
                (add_right_comm (∑ i in s, A i) T (-(∑ i in s, B i)))
                (congrArg
                  (fun z : ℂ => z + T)
                  (sum_sub_sum_eq_add_neg_sum s A B).symm))
    _ = (∑ i in s, (A i - B i)) + T := by
          exact
            congrArg
              (fun z : ℂ => z + T)
              (Finset.sum_sub_distrib.symm)

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
          exact
            congrArg
              (fun z : ℝ => z + η * b)
              (Finset.mul_sum (s := s) (f := a) η).symm
    _ = η * ((∑ i in s, a i) + b) := by
          exact (mul_add η (∑ i in s, a i) b).symm

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
          exact (Finset.mul_sum (s := s) (f := a) η).symm

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
          exact (Finset.mul_sum (s := s) (f := fun i => a i) (η * ρ)).symm
    _ = η * ρ * (∑ i in s, a i) := rfl

/-- The final scalar normalization for the angle-grid chord estimate. -/
theorem eta_mul_radius_mul_pi_eq_eta_mul_pi_mul_radius
    (η ρ : ℝ) :
    η * ρ * Real.pi = η * (Real.pi * ρ) := by
  calc
    η * ρ * Real.pi = η * (ρ * Real.pi) := mul_assoc η ρ Real.pi
    _ = η * (Real.pi * ρ) := by
          exact congrArg (fun z : ℝ => η * z) (mul_comm ρ Real.pi)

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
      exact congrArg (fun n : ℕ => n + 1) (Nat.add_sub_cancel' hjm)

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
      exact congrArg (fun n : ℕ => j + n) (Nat.add_comm t 1)
    _ = j + 1 + t := by
      exact (Nat.add_assoc j 1 t).symm

/-- The right-semicircle angle interval has total length `π`. -/
theorem pi_div_two_sub_neg_pi_div_two :
    Real.pi / 2 - (-(Real.pi / 2)) = Real.pi := by
  calc
      Real.pi / 2 - (-(Real.pi / 2))
          = Real.pi / 2 + Real.pi / 2 := sub_neg_eq_add _ _
      _ = 2 * (Real.pi / 2) := (two_mul (Real.pi / 2)).symm
      _ = (2 * Real.pi) / 2 := by
        exact Eq.symm (mul_div_assoc (2 : ℝ) Real.pi 2)
      _ = Real.pi := mul_div_cancel_left₀ Real.pi (two_ne_zero' ℝ)

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
  calc
    r • A = ((r : ℝ) : ℂ) * A :=
      RCLike.real_smul_eq_coe_mul r A
    _ = A * ((r : ℝ) : ℂ) :=
      mul_comm ((r : ℝ) : ℂ) A

/-- Multiplication by `I` factors out of a difference. -/
theorem Complex.I_mul_sub_factor
    (A B : ℂ) :
    Complex.I * A - Complex.I * B =
      Complex.I * (A - B) :=
  (mul_sub Complex.I A B).symm

/-- Multiplication by `I` preserves the complex norm. -/
theorem Complex.norm_I_mul
    (A : ℂ) :
    ‖Complex.I * A‖ = ‖A‖ := by
  calc
    ‖Complex.I * A‖ = ‖Complex.I‖ * ‖A‖ :=
      norm_mul Complex.I A
    _ = (1 : ℝ) * ‖A‖ :=
      congrArg (fun r : ℝ => r * ‖A‖) Complex.norm_I
    _ = ‖A‖ :=
      one_mul ‖A‖

/-- The range `0, ..., m` is nonempty, witnessed by `0`. -/
theorem zero_mem_range_nat_succ
    (m : ℕ) :
    0 ∈ Finset.range (m + 1) :=
  Finset.mem_range.mpr (Nat.succ_pos m)

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
      exact
        Eq.trans
          (mul_sub A ((safe - prev : ℝ) : ℂ) ((rnext - rcur : ℝ) : ℂ)).symm
          (congrArg
            (fun z : ℂ => A * z)
            (Complex.ofReal_sub (safe - prev) (rnext - rcur)).symm)
    _ =
      A * ((((safe - rnext) - (prev - rcur) : ℝ) : ℂ)) := by
      exact
        congrArg
          (fun z : ℝ => A * ((z : ℝ) : ℂ))
          (real_safe_endpoint_cell_error_scalar safe prev rnext rcur)
    _ =
      A * (((safe - rnext : ℝ) : ℂ)) -
        A * (((prev - rcur : ℝ) : ℂ)) := by
      exact
        Eq.trans
          (congrArg
            (fun z : ℂ => A * z)
            (Complex.ofReal_sub (safe - rnext) (prev - rcur)))
          (mul_sub A ((safe - rnext : ℝ) : ℂ) ((prev - rcur : ℝ) : ℂ))

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
          exact
            congrArg (fun z : ℂ => A * z)
              (Eq.trans
                (congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (zero_sub B))
                (Complex.ofReal_neg B))
    _ = -(A * (B : ℂ)) := mul_neg A (B : ℂ)
    _ = -A * (B : ℂ) := (neg_mul A (B : ℂ)).symm
    _ = -A * (((B - 0 : ℝ) : ℂ)) := by
          exact
            congrArg (fun z : ℂ => -A * z)
              (Eq.symm
                (congrArg (fun x : ℝ => ((x : ℝ) : ℂ)) (sub_zero B)))

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
  have hrad :
      ρ ^ 2 - (ρ * Real.sin θ) ^ 2 = (ρ * Real.cos θ) ^ 2 := by
    exact radius_sq_sub_radius_mul_sin_sq_eq_radius_mul_cos_sq ρ θ
  show Real.sqrt (ρ ^ 2 - (ρ * Real.sin θ) ^ 2) = ρ * Real.cos θ
  exact
    Eq.trans
      (congrArg Real.sqrt hrad)
      (Real.sqrt_sq hmul_nonneg)

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
  have hre :
      (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)).re =
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re := by
    calc
      (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)).re =
          c.re + Complex.rightSemicircleGraphRe ρ (ρ * Real.sin θ) :=
        Complex.rightSemicircleGraphPoint_re c ρ (ρ * Real.sin θ)
      _ = c.re + ρ * Real.cos θ :=
        congrArg (fun x : ℝ => c.re + x) hgraph
      _ = (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re :=
        Eq.symm (Complex.add_realRadius_exp_I_mul_re c ρ θ)
  have him :
      (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)).im =
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
    calc
      (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)).im =
          c.im + ρ * Real.sin θ :=
        Complex.rightSemicircleGraphPoint_im c ρ (ρ * Real.sin θ)
      _ = (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im :=
        Eq.symm (Complex.add_realRadius_exp_I_mul_im c ρ θ)
  exact Complex.ext hre him

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
  exact hsin ▸ Complex.rightSemicircleGraphPoint_eq_angle c hρ hθ

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
  exact hsin ▸ Complex.rightSemicircleGraphRe_mul_sin_eq_mul_cos hρ.le hθ

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
  show
    (∑ k in Finset.range (m + 1),
      f (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m k)) *
        (((Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k) : ℝ) : ℂ))) =
      ∑ k in Finset.range (m + 1),
        f (c + (ρ : ℂ) *
          Complex.exp (Complex.I *
            (Complex.rightSemicircleAngleGrid ρ m k : ℂ))) *
        (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
           ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ))
  exact
    Finset.sum_congr rfl
      (fun k hk =>
        let hk0 : k ∈ Finset.range (m + 2) :=
          Complex.staircase_lower_sample_mem_range hk
        let hk1 : k + 1 ∈ Finset.range (m + 2) :=
          Complex.staircase_upper_sample_mem_range hk
        let hpoint :
            Complex.rightSemicircleGraphPoint c ρ
              (Complex.rightSemicircleStaircaseY ρ m k) =
            c + (ρ : ℂ) *
              Complex.exp (Complex.I *
                (Complex.rightSemicircleAngleGrid ρ m k : ℂ)) :=
          Complex.rightSemicircleGraphPoint_eq_angleGrid c hρ hk0
        let hright :
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m (k + 1)) =
            ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) :=
          Complex.rightSemicircleGraphRe_eq_angleGrid_cos hρ hk1
        let hleft :
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k) =
            ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) :=
          Complex.rightSemicircleGraphRe_eq_angleGrid_cos hρ hk0
        let hdiff :
            Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m (k + 1)) -
              Complex.rightSemicircleGraphRe ρ
                (Complex.rightSemicircleStaircaseY ρ m k) =
            ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
              ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) :=
          congrArg₂ HSub.hSub hright hleft
        congrArg₂
          (fun z q : ℂ => f z * q)
          hpoint
          (congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) hdiff))

/-- A real norm hypothesis can be read as the corresponding absolute-value
hypothesis. -/
theorem Real.abs_le_of_norm_le
    {x δ : ℝ}
    (h : ‖x‖ ≤ δ) :
    |x| ≤ δ :=
  (Real.norm_eq_abs x) ▸ h

/-- A real norm strict bound can be read as the corresponding absolute-value
strict bound. -/
theorem Real.abs_lt_of_norm_lt
    {x ε : ℝ}
    (h : ‖x‖ < ε) :
    |x| < ε :=
  (Real.norm_eq_abs x) ▸ h

/-- The norm of a reversed real difference is the same as the metric distance. -/
theorem Real.norm_sub_eq_dist_comm
    (x y : ℝ) :
    ‖y - x‖ = dist x y := by
  calc
    ‖y - x‖ = dist y x :=
      Eq.symm (dist_eq_norm y x)
    _ = dist x y :=
      dist_comm y x

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
          (continuous_const.mul Complex.continuous_ofReal)))).continuousOn
  have hmaps :
      Set.MapsTo
        (fun θ : ℝ =>
          c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro θ hθ
    exact
      Complex.rightSemicircleAnglePoint_mem_core c hρ
        (rightSemicircleAngle_uIcc_eq_Icc.symm ▸ hθ)
  exact hcont.comp hparam hmaps

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
    (Complex.continuous_ofReal.comp
      (continuous_const.mul Real.continuous_sin)).continuousOn
  have hprod_Icc :
      ContinuousOn
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    hprobe.mul hdx
  have hprod_uIcc :
      ContinuousOn
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)))
        [[-(Real.pi / 2), Real.pi / 2]] :=
    Eq.subst
      (motive := fun s : Set ℝ =>
        ContinuousOn
          (fun θ : ℝ =>
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (((-ρ * Real.sin θ : ℝ) : ℂ)))
          s)
      (Eq.symm rightSemicircleAngle_uIcc_eq_Icc)
      hprod_Icc
  exact hprod_uIcc.intervalIntegrable

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
    (Complex.continuous_ofReal.comp
      (continuous_const.mul Real.continuous_cos)).continuousOn
  have hprod_Icc :
      ContinuousOn
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ))
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    hprobe.mul hdy
  have hprod_uIcc :
      ContinuousOn
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ))
        [[-(Real.pi / 2), Real.pi / 2]] :=
    Eq.subst
      (motive := fun s : Set ℝ =>
        ContinuousOn
          (fun θ : ℝ =>
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              ((ρ * Real.cos θ : ℝ) : ℂ))
          s)
      (Eq.symm rightSemicircleAngle_uIcc_eq_Icc)
      hprod_Icc
  exact hprod_uIcc.intervalIntegrable

/-- Pointwise scalar substitution from the graph height coordinate to the angle
coordinate in the vertical `dy` component. -/
theorem Complex.rightSemicircleGraphScalarAngleIntegrand_eq
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ θ : ℝ}
    (hρ : 0 < ρ)
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    (ρ * Real.cos θ) •
        f (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)) =
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        ((ρ * Real.cos θ : ℝ) : ℂ) := by
  have hpoint :
      Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ) =
        c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) :=
    Complex.rightSemicircleGraphPoint_eq_angle c hρ hθ
  exact
    (congrArg f hpoint).symm ▸
      complex_real_smul_eq_mul_right
        (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
        (ρ * Real.cos θ)

/-- Scalar substitution from the vertical graph coordinate
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
    exact (Real.hasDerivAt_sin θ).const_mul ρ
  have hφ_deriv_cont :
      ContinuousOn (fun θ : ℝ => ρ * Real.cos θ) [[a, b]] := by
    exact (continuous_const.mul Real.continuous_cos).continuousOn
  have hG_base :
      ContinuousOn G (Set.Icc (-ρ) ρ) := by
    exact
      Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
        f c hρ hcont
  have hG_image :
      ContinuousOn G (φ '' [[a, b]]) := by
    exact
      hG_base.mono
        (fun y hy =>
          match hy with
          | ⟨θ, _hθ, hθy⟩ =>
              Eq.subst
                (motive := fun t : ℝ => t ∈ Set.Icc (-ρ) ρ)
                hθy
                (radius_mul_sin_mem_height_Icc hρ.le))
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
    exact radius_mul_sin_neg_pi_div_two ρ
  have hφb : φ b = ρ := by
    exact radius_mul_sin_pi_div_two ρ
  calc
    (∫ y : ℝ in (-ρ)..ρ, G y) =
        ∫ y : ℝ in φ a..φ b, G y := by
      exact
        (congrArg₂
          (fun u v : ℝ => ∫ y : ℝ in u..v, G y)
          hφa hφb).symm
    _ = ∫ θ : ℝ in a..b, (ρ * Real.cos θ) • (G (φ θ)) :=
      hsubst.symm
    _ =
        ∫ θ : ℝ in a..b,
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      show
        (ρ * Real.cos θ) •
          f (Complex.rightSemicircleGraphPoint c ρ (ρ * Real.sin θ)) =
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          ((ρ * Real.cos θ : ℝ) : ℂ)
      exact Complex.rightSemicircleGraphScalarAngleIntegrand_eq f c hρ hθ

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
  show
    Complex.I *
      (∫ y : ℝ in (-ρ)..ρ,
        f (Complex.rightSemicircleGraphPoint c ρ y)) =
      Complex.I *
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            ((ρ * Real.cos θ : ℝ) : ℂ)
  exact
    congrArg
      (fun z : ℂ => Complex.I * z)
      (Complex.rightSemicircleGraphScalarIntegral_eq_angle_dy f c hρ hcont)

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
    exact
      intervalIntegral.integral_congr
        (fun θ _hθ =>
          rightSemicircleAngle_tangentFactor_decompose
            (f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ρ θ)
  have hadd :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fx θ + Complex.I * Fy θ) =
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fx θ) +
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Complex.I * Fy θ :=
    intervalIntegral.integral_add hFx (hFy.const_mul Complex.I)
  have hconst :
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Complex.I * Fy θ) =
        Complex.I *
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fy θ :=
    intervalIntegral.integral_const_mul Complex.I Fy
  show
    (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) *
          Complex.exp (Complex.I * (θ : ℂ)))) =
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fx θ) +
        Complex.I *
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fy θ)
  exact Eq.trans hpoint (Eq.trans hadd (congrArg (fun z : ℂ =>
    (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2), Fx θ) + z) hconst))

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
  show
    Complex.rightSemicircleAngleIntegral f c ρ -
      Complex.rightSemicircleGraphVerticalIntegral f c ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (((-ρ * Real.sin θ : ℝ) : ℂ))
  exact horizontal_component_eq_of_angle_and_vertical_eq hangle hvertical

end
end LFunctions
end Boundary
