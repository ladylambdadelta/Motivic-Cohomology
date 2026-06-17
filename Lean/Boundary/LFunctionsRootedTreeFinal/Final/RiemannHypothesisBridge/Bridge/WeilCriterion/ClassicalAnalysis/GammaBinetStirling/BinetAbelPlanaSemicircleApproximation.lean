import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleEndpointDefect

/-!
# Semicircle graph approximation for finite-height Abel-Plana collars

This file owns the staircase-to-arc convergence theorem and the resulting
right-half-core Cauchy-Goursat wrapper consumed by finite-hole boundary accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- An eventual natural-number statement supplies a concrete tail witness. -/
theorem exists_nat_tail_of_eventually_atTop
    {P : ℕ → Prop}
    (hP : ∀ᶠ n : ℕ in atTop, P n) :
    ∃ N : ℕ, ∀ n ≥ N, P n :=
  eventually_atTop.mp hP

/-- The left endpoint belongs to the unordered closed interval it spans. -/
theorem real_left_mem_uIcc
    (a b : ℝ) :
    a ∈ [[a, b]] := by
  match le_total a b with
  | Or.inl hab =>
      exact Set.mem_uIcc.mpr (Or.inl (And.intro le_rfl hab))
  | Or.inr hba =>
      exact Set.mem_uIcc.mpr (Or.inr (And.intro hba le_rfl))

/-- The right endpoint belongs to the unordered closed interval it spans. -/
theorem real_right_mem_uIcc
    (a b : ℝ) :
    b ∈ [[a, b]] := by
  match le_total a b with
  | Or.inl hab =>
      exact Set.mem_uIcc.mpr (Or.inl (And.intro hab le_rfl))
  | Or.inr hba =>
      exact Set.mem_uIcc.mpr (Or.inr (And.intro le_rfl hba))

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
  let ⟨δ, hδ, hδ_modulus⟩ :=
    Metric.uniformContinuousOn_iff.mp hgraph_uniform ε hε
  have hmesh :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
            Complex.rightSemicircleStaircaseY ρ m k| < δ :=
    Complex.eventually_rightSemicircleStaircase_cell_length_lt hρ hδ
  filter_upwards [hmesh] with m hm k hk y hy
  let ⟨yₛ, hyₛ_cell, hsafe⟩ :=
    Complex.exists_rightSemicircleStaircaseSafeRe_eq_graphRe_of_cell
      hρ m k hk
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
  have hclose_safe :
      dist (Complex.rightSemicircleGraphRe ρ y)
        (Complex.rightSemicircleStaircaseSafeRe ρ m k) < ε :=
    hsafe.symm ▸ hgraph_close
  exact
    (Real.norm_sub_eq_dist_comm
      (Complex.rightSemicircleGraphRe ρ y)
      (Complex.rightSemicircleStaircaseSafeRe ρ m k)) ▸
      hclose_safe

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
  match em (k = 0) with
  | Or.inl hk0 =>
    subst k
    have hy0 : Complex.rightSemicircleStaircaseY ρ m 0 = -ρ :=
      Complex.rightSemicircleStaircaseY_zero ρ m
    have hprev0 :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 :=
      Complex.rightSemicircleStaircasePrevSafeRe_zero ρ m
    have hgraph0 :
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m 0) = 0 :=
      hy0 ▸ (Complex.rightSemicircleGraphRe_bottom (ρ := ρ))
    have hdiff :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m 0) = 0 := by
      calc
        Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 -
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m 0) =
            0 - 0 :=
          congrArg₂ HSub.hSub hprev0 hgraph0
        _ = 0 :=
          sub_self 0
    have hzero_norm : ‖(0 : ℝ)‖ < ε := by
      calc
        ‖(0 : ℝ)‖ = 0 := norm_zero
        _ < ε := hε
    exact hdiff ▸ hzero_norm
  | Or.inr hk0 =>
    have hk_pred : k - 1 ∈ Finset.range (m + 1) := by
      exact Complex.staircase_pred_mem_range_of_ne_zero hk hk0
    have hsucc : (k - 1) + 1 = k :=
      Complex.staircase_pred_succ_of_ne_zero hk0
    have hy_mem :
        Complex.rightSemicircleStaircaseY ρ m k ∈
          [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
            Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)]] := by
      have htop :
          Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1) =
            Complex.rightSemicircleStaircaseY ρ m k :=
        congrArg (fun n : ℕ => Complex.rightSemicircleStaircaseY ρ m n) hsucc
      exact
        Eq.subst
          (motive := fun top : ℝ =>
            Complex.rightSemicircleStaircaseY ρ m k ∈
              [[Complex.rightSemicircleStaircaseY ρ m (k - 1), top]])
          (Eq.symm htop)
          (real_right_mem_uIcc
            (Complex.rightSemicircleStaircaseY ρ m (k - 1))
            (Complex.rightSemicircleStaircaseY ρ m k) :
            Complex.rightSemicircleStaircaseY ρ m k ∈
              [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
                Complex.rightSemicircleStaircaseY ρ m k]])
    have happrox :=
      hm (k - 1) hk_pred
        (Complex.rightSemicircleStaircaseY ρ m k) hy_mem
    have hprev :
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
          Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) := by
      exact
        Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero
          ρ m k hk0
    exact hprev.symm ▸ happrox

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
  exact
    hdist.trans
      (Eq.symm
        (Real.norm_eq_abs
          (Complex.rightSemicircleStaircaseSafeRe ρ m k -
            Complex.rightSemicircleGraphRe ρ y)))

/-- A horizontal connector point is close to the graph sample if both endpoint
safe coordinates are close to that graph real-coordinate. -/
theorem Complex.dist_rightSemicircleHorizontalPoint_graphPoint_le
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ)
    {x δ : ℝ}
    (_hδ : 0 ≤ δ)
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
    exact Real.abs_le_of_norm_le hprev
  have hsafe_abs :
      |Complex.rightSemicircleStaircaseSafeRe ρ m k - g| ≤ δ := by
    exact Real.abs_le_of_norm_le hsafe
  have hx_abs : |x - g| ≤ δ := by
    exact abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le hx hprev_abs hsafe_abs
  have hdist :
      dist
        ((((c.re + x : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        (Complex.rightSemicircleGraphPoint c ρ
          (Complex.rightSemicircleStaircaseY ρ m k)) =
        |x - g| := by
    exact
      Complex.dist_realLinePoint_rightSemicircleGraphPoint
        c ρ x (Complex.rightSemicircleStaircaseY ρ m k)
  exact hdist.symm ▸ hx_abs

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
    have hnorm_zero :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m m - 0‖ ≤ δ := by
      exact (congrArg (fun x : ℝ =>
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m m - x‖) hzero) ▸ hsafe
    have hnorm :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m m‖ ≤ δ :=
      (congrArg (fun x : ℝ => ‖x‖ ≤ δ)
        (Eq.symm (sub_zero (Complex.rightSemicircleStaircaseSafeRe ρ m m)))) ▸
        hnorm_zero
    exact Real.abs_le_of_norm_le hnorm
  have hsafe_abs_zero :
      |Complex.rightSemicircleStaircaseSafeRe ρ m m - 0| ≤ δ := by
    exact (congrArg (fun x : ℝ => |x| ≤ δ)
      (Eq.symm (sub_zero (Complex.rightSemicircleStaircaseSafeRe ρ m m)))) ▸
      hsafe_abs
  have hzero_abs_zero : |(0 : ℝ) - 0| ≤ δ := by
    have hzero_abs : |(0 : ℝ)| ≤ δ :=
      (congrArg (fun x : ℝ => x ≤ δ) (Eq.symm (abs_zero : |(0 : ℝ)| = 0))) ▸
        hδ
    exact (congrArg (fun x : ℝ => |x| ≤ δ) (Eq.symm (sub_self 0))) ▸
      hzero_abs
  have hx_abs : |x| ≤ δ := by
    have hx_abs_zero :
        |x - 0| ≤ δ :=
      abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le
        hx hsafe_abs_zero hzero_abs_zero
    exact (congrArg (fun z : ℝ => |z| ≤ δ) (Eq.symm (sub_zero x))) ▸ hx_abs_zero
  have hdist :
      dist
        ((((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        (Complex.rightSemicircleGraphPoint c ρ ρ) =
        |x| := by
    have hraw :=
      Complex.dist_realLinePoint_rightSemicircleGraphPoint c ρ x ρ
    have habs :
        |x - Complex.rightSemicircleGraphRe ρ ρ| = |x| := by
      exact (congrArg (fun z : ℝ => |x - z|) hzero).trans
        (congrArg abs (sub_zero x))
    exact hraw.trans habs
  exact hdist.symm ▸ hx_abs

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
  match Metric.uniformContinuousOn_iff.mp hf_uniform ε hε with
  | ⟨δ, hδ, hδ_modulus⟩ =>
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
    exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy_Icc
  have hdist :
      dist zₛ zᵧ < δ := by
    have hdist_eq :
        dist zₛ zᵧ =
          ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
            Complex.rightSemicircleGraphRe ρ y‖ :=
      Complex.dist_rightSemicircleStaircasePoint_graphPoint c ρ m k y
    exact hdist_eq ▸ hm k hk y hy
  have hclose : dist (f zₛ) (f zᵧ) < ε :=
    hδ_modulus zₛ hzₛ zᵧ hzᵧ hdist
  show ‖f zₛ - f zᵧ‖ ≤ ε
  exact (dist_eq_norm (f zₛ) (f zᵧ)) ▸ le_of_lt hclose

/-- One vertical staircase cell is controlled by the uniform integrand error
times its height. -/
theorem Complex.norm_rightSemicircleStaircaseVertical_cell_sub_graph_cell_le
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (_hρ : 0 < ρ)
    (_hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (m k : ℕ)
    (_hk : k ∈ Finset.range (m + 1))
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
    (_hη_nonneg : 0 ≤ η)
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
      show
        (∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ)))) -
          (∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (Complex.rightSemicircleGraphPoint c ρ y)) =
          ∫ y : ℝ in
            Complex.rightSemicircleStaircaseY ρ m k..
              Complex.rightSemicircleStaircaseY ρ m (k + 1),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (((c.im + y : ℝ) : ℂ))) -
              f (Complex.rightSemicircleGraphPoint c ρ y)
      exact Eq.symm (intervalIntegral.integral_sub hS hG)
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          ‖z‖ ≤
            η *
              |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
                Complex.rightSemicircleStaircaseY ρ m k|)
        (Eq.symm hintegral)
        (Complex.norm_rightSemicircleStaircaseVertical_cell_sub_graph_cell_le
          f c hρ hcont m k hk (happrox k hk))
  have hsum_error :
      ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖
        ≤ η * (2 * ρ) := by
    calc
      ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖
          = ‖∑ k in Finset.range (m + 1), (S k - G k)‖ := by
            exact congrArg norm (Finset.sum_sub_distrib.symm)
      _ ≤ ∑ k in Finset.range (m + 1), ‖S k - G k‖ :=
            norm_sum_le _ _
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
            exact
              congrArg
                (fun x : ℝ => η * x)
                (Complex.sum_rightSemicircleStaircase_cell_lengths hρ.le m)
  have hstair :
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) =
        Complex.I * ∑ k in Finset.range (m + 1), S k := by
    show
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) =
        Complex.I *
          ∑ k in Finset.range (m + 1),
            ∫ y : ℝ in
              Complex.rightSemicircleStaircaseY ρ m k..
                Complex.rightSemicircleStaircaseY ρ m (k + 1),
              f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                Complex.I * (((c.im + y : ℝ) : ℂ)))
    exact
      Complex.sum_rightSemicircleStaircaseVerticalIntegral_eq_I_mul_sum
        f c ρ m
  have hgraph :
      Complex.rightSemicircleGraphVerticalIntegral f c ρ =
        Complex.I * ∑ k in Finset.range (m + 1), G k := by
    show
      Complex.rightSemicircleGraphVerticalIntegral f c ρ =
        Complex.I *
          ∑ k in Finset.range (m + 1),
            ∫ y : ℝ in
              Complex.rightSemicircleStaircaseY ρ m k..
                Complex.rightSemicircleStaircaseY ρ m (k + 1),
              f (Complex.rightSemicircleGraphPoint c ρ y)
    exact
      Complex.rightSemicircleGraphVerticalIntegral_eq_sum_cells
        f c hρ hcont m
  calc
    ‖(∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
      Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
        =
      ‖Complex.I *
        ((∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k))‖ := by
          exact
            Eq.trans
              (congrArg
                (fun z : ℂ => ‖z - Complex.rightSemicircleGraphVerticalIntegral f c ρ‖)
                hstair)
              (Eq.trans
                (congrArg
                  (fun z : ℂ =>
                    ‖Complex.I * (∑ k in Finset.range (m + 1), S k) - z‖)
                  hgraph)
                (congrArg norm
                  (Complex.I_mul_sub_factor
                    (∑ k in Finset.range (m + 1), S k)
                    (∑ k in Finset.range (m + 1), G k))))
    _ = ‖(∑ k in Finset.range (m + 1), S k) -
          (∑ k in Finset.range (m + 1), G k)‖ := by
          exact
            Complex.norm_I_mul
              ((∑ k in Finset.range (m + 1), S k) -
                (∑ k in Finset.range (m + 1), G k))
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
  exact Metric.tendsto_atTop.mpr (fun ε hε => by
    have htwoρ_pos : 0 < 2 * ρ :=
      real_two_mul_pos_of_pos hρ
    let η : ℝ := (ε / 2) / (2 * ρ)
    have hε_half_pos : 0 < ε / 2 :=
      half_pos hε
    have hη_pos : 0 < η :=
      div_pos hε_half_pos htwoρ_pos
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
    match eventually_atTop.mp hevent with
    | Exists.intro N hN =>
      exact Exists.intro N (fun m hmN => by
        have hm :
            ∀ k ∈ Finset.range (m + 1),
              ∀ y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
                      Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
                ‖f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                      Complex.I * (((c.im + y : ℝ) : ℂ))) -
                  f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ η :=
          hN m hmN
        have hbound :
            ‖(∑ k in Finset.range (m + 1),
                Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
              Complex.rightSemicircleGraphVerticalIntegral f c ρ‖
              ≤ η * (2 * ρ) :=
          Complex.norm_sum_rightSemicircleStaircaseVertical_sub_graphVertical_le
            f c hρ hcont m hη_nonneg hm
        have hη_eq : η * (2 * ρ) = ε / 2 := by
          show ((ε / 2) / (2 * ρ)) * (2 * ρ) = ε / 2
          exact div_mul_cancel_of_pos_right htwoρ_pos
        have hη_lt : η * (2 * ρ) < ε :=
          Eq.subst
            (motive := fun x : ℝ => x < ε)
            (Eq.symm hη_eq)
            (half_lt_self hε)
        have hnorm_lt :
            ‖(∑ k in Finset.range (m + 1),
                Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
              Complex.rightSemicircleGraphVerticalIntegral f c ρ‖ < ε :=
          lt_of_le_of_lt hbound hη_lt
        have hdist_norm :
            dist
              (∑ k in Finset.range (m + 1),
                Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)
              (Complex.rightSemicircleGraphVerticalIntegral f c ρ) =
            ‖(∑ k in Finset.range (m + 1),
                Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) -
              Complex.rightSemicircleGraphVerticalIntegral f c ρ‖ :=
          dist_eq_norm
            (∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)
            (Complex.rightSemicircleGraphVerticalIntegral f c ρ)
        exact
          Eq.subst
            (motive := fun x : ℝ => x < ε)
            (Eq.symm hdist_norm)
            hnorm_lt))

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
  match Metric.uniformContinuousOn_iff.mp hf_uniform ε hε with
  | ⟨δ, hδ, hδ_modulus⟩ =>
  let δ₀ : ℝ := δ / 2
  have hδ₀_pos : 0 < δ₀ := by
    show 0 < δ / 2
    exact half_pos hδ
  have hδ₀_nonneg : 0 ≤ δ₀ := le_of_lt hδ₀_pos
  have hδ₀_lt : δ₀ < δ := by
    show δ / 2 < δ
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
      exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
    have hsafe_at_sample :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ₀ := by
      have hy_sample :
          Complex.rightSemicircleStaircaseY ρ m k ∈
            [[Complex.rightSemicircleStaircaseY ρ m k,
              Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
        real_left_mem_uIcc
          (Complex.rightSemicircleStaircaseY ρ m k)
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))
      exact le_of_lt (hm_safe k hk
        (Complex.rightSemicircleStaircaseY ρ m k) hy_sample)
    have hprev_at_sample :
        ‖Complex.rightSemicircleStaircasePrevSafeRe ρ m k -
          Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k)‖ ≤ δ₀ :=
      le_of_lt (hm_prev k hk)
    have hdist_le :
        dist zₓ zᵧ ≤ δ₀ := by
      exact
        Complex.dist_rightSemicircleHorizontalPoint_graphPoint_le
          c ρ m k hδ₀_nonneg hx hprev_at_sample hsafe_at_sample
    have hdist_lt : dist zₓ zᵧ < δ :=
      lt_of_le_of_lt hdist_le hδ₀_lt
    have hclose : dist (f zₓ) (f zᵧ) < ε :=
      hδ_modulus zₓ hzₓ zᵧ hzᵧ hdist_lt
    show ‖f zₓ - f zᵧ‖ ≤ ε
    exact (dist_eq_norm (f zₓ) (f zᵧ)) ▸ le_of_lt hclose
  · intro x hx
    let zₓ : ℂ :=
      (((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + ρ : ℝ) : ℂ)))
    let zᵧ : ℂ := Complex.rightSemicircleGraphPoint c ρ ρ
    have hzₓ :
        zₓ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      exact
        Complex.rightSemicircleStaircaseTopConnector_subset_core
          c hρ m hx
    have hy : ρ ∈ Set.Icc (-ρ) ρ := by
      exact Complex.radius_mem_semicircle_height_Icc hρ.le
    have hzᵧ :
        zᵧ ∈ Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
      exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
    have hm_mem : m ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr (Nat.lt_succ_self m)
    have hy_top :
        ρ ∈
          [[Complex.rightSemicircleStaircaseY ρ m m,
            Complex.rightSemicircleStaircaseY ρ m (m + 1)]] := by
      exact
        Eq.subst
          (motive := fun top : ℝ =>
            ρ ∈ [[Complex.rightSemicircleStaircaseY ρ m m, top]])
          (Eq.symm (Complex.rightSemicircleStaircaseY_last ρ m))
          (real_right_mem_uIcc
            (Complex.rightSemicircleStaircaseY ρ m m) ρ :
            ρ ∈ [[Complex.rightSemicircleStaircaseY ρ m m, ρ]])
    have hsafe_top :
        ‖Complex.rightSemicircleStaircaseSafeRe ρ m m -
          Complex.rightSemicircleGraphRe ρ ρ‖ ≤ δ₀ :=
      le_of_lt (hm_safe m hm_mem ρ hy_top)
    have hdist_le :
        dist zₓ zᵧ ≤ δ₀ := by
      exact
        Complex.dist_rightSemicircleTopConnectorPoint_graphPoint_le
          c m hδ₀_nonneg hx hsafe_top
    have hdist_lt : dist zₓ zᵧ < δ :=
      lt_of_le_of_lt hdist_le hδ₀_lt
    have hclose : dist (f zₓ) (f zᵧ) < ε :=
      hδ_modulus zₓ hzₓ zᵧ hzᵧ hdist_lt
    show ‖f zₓ - f zᵧ‖ ≤ ε
    exact (dist_eq_norm (f zₓ) (f zᵧ)) ▸ le_of_lt hclose

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
        show (1 / 2 : ℕ) ≤ 0
        exact one_div_two_nat_le_zero
    | succ m =>
        show (m + 2) / 2 ≤ m + 1
        exact Nat.div_le_of_le_mul' (nat_succ_succ_le_two_mul_succ m)
  exact
    Complex.rightSemicircleStaircaseSafeRe_totalHorizontalVariation_le_two_radius_of_unimodal
      hρ m j hjm
      (by
        show
          ∀ k,
            k < (m + 1) / 2 →
              Complex.rightSemicircleStaircaseSafeRe ρ m k ≤
                Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1)
        exact Complex.rightSemicircleStaircaseSafeRe_monotone_prefix_midpoint
          hρ m)
      (by
        show
          ∀ k,
            (m + 1) / 2 ≤ k →
              k < m →
                Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
                  Complex.rightSemicircleStaircaseSafeRe ρ m k
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
  let H : ℝ → ℂ := fun x =>
    f ((((c.re + x : ℝ) : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
  let F : ℝ → ℂ := fun x =>
    H x - f z₀
  have hmain :
      Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k -
        f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, F x := by
    show
      (∫ x : ℝ in a..b, H x) - f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, H x - f z₀
    exact
      interval_integral_sub_const_sample_eq_integral_sub_const
        H (f z₀) a b
        (Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
          f c hρ m k hk hcont)
  exact
    hmain.symm ▸
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
  let H : ℝ → ℂ := fun x =>
    f ((((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ))))
  let F : ℝ → ℂ := fun x =>
    H x - f z₀
  have hmain :
      Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m -
        f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, F x := by
    show
      (∫ x : ℝ in a..b, H x) - f z₀ * (((b - a : ℝ) : ℂ)) =
        ∫ x : ℝ in a..b, H x - f z₀
    exact
      interval_integral_sub_const_sample_eq_integral_sub_const
        H (f z₀) a b
        (Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
          f c hρ m hcont)
  exact
    hmain.symm ▸
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
  let H : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k
  let S : ℕ → ℂ := fun k =>
    f (Complex.rightSemicircleGraphPoint c ρ
        (Complex.rightSemicircleStaircaseY ρ m k)) *
      (((Complex.rightSemicircleStaircaseSafeRe ρ m k -
         Complex.rightSemicircleStaircasePrevSafeRe ρ m k : ℝ) : ℂ))
  let T : ℂ :=
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m
  let Stop : ℂ :=
    f (Complex.rightSemicircleGraphPoint c ρ ρ) *
      (((0 - Complex.rightSemicircleStaircaseSafeRe ρ m m : ℝ) : ℂ))
  let E : ℕ → ℂ := fun k => H k - S k
  let Etop : ℂ := T - Stop
  have hdecomp :
      ((∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m =
        (∑ k in Finset.range (m + 1), E k) + Etop := by
    show
      ((∑ k in Finset.range (m + 1), H k) + T) -
        ((∑ k in Finset.range (m + 1), S k) + Stop) =
        (∑ k in Finset.range (m + 1), E k) + Etop
    have hsplit :
      ((∑ k in Finset.range (m + 1), H k) + T) -
        ((∑ k in Finset.range (m + 1), S k) + Stop) =
        ((∑ k in Finset.range (m + 1), H k) -
          (∑ k in Finset.range (m + 1), S k)) + Etop :=
      horizontal_top_sample_error_decompose
        (∑ k in Finset.range (m + 1), H k)
        T
        (∑ k in Finset.range (m + 1), S k)
        Stop
    have hsum :
      ((∑ k in Finset.range (m + 1), H k) -
        (∑ k in Finset.range (m + 1), S k)) =
        ∑ k in Finset.range (m + 1), E k :=
      Eq.symm
        (Finset.sum_sub_distrib
          (s := Finset.range (m + 1))
          (f := H)
          (g := S))
    exact
      Eq.trans hsplit
        (congrArg
          (fun z : ℂ => z + Etop)
          hsum)
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
            exact add_le_add_right (norm_sum_le _ _) _
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
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ η * (2 * ρ))
      (Eq.symm hdecomp)
      (le_trans hnorm (mul_le_mul_of_nonneg_left hvar hη_nonneg))

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
  exact Metric.tendsto_atTop.mpr (fun ε hε => by
    have htwoρ_pos : 0 < 2 * ρ :=
      real_two_mul_pos_of_pos hρ
    let η : ℝ := (ε / 2) / (2 * ρ)
    have hε_half_pos : 0 < ε / 2 :=
      half_pos hε
    have hη_pos : 0 < η :=
      div_pos hε_half_pos htwoρ_pos
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
    match eventually_atTop.mp hevent with
    | Exists.intro N hN =>
      exact Exists.intro N (fun m hmN => by
        have hm :
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
          hN m hmN
        have hbound :
            ‖((∑ k in Finset.range (m + 1),
                Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
                Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
              Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m‖
              ≤ η * (2 * ρ) :=
          Complex.norm_sum_rightSemicircleStaircaseHorizontal_sub_sampleSum_le
            f c hρ hcont m hη_nonneg hm
        have hη_eq : η * (2 * ρ) = ε / 2 := by
          show ((ε / 2) / (2 * ρ)) * (2 * ρ) = ε / 2
          exact div_mul_cancel_of_pos_right htwoρ_pos
        have hη_lt : η * (2 * ρ) < ε :=
          Eq.subst
            (motive := fun x : ℝ => x < ε)
            (Eq.symm hη_eq)
            (half_lt_self hε)
        let A : ℂ :=
          ((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
              Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m
        have hdist_norm : dist A 0 = ‖A‖ := by
          calc
            dist A 0 = ‖A - 0‖ := dist_eq_norm A 0
            _ = ‖A‖ := congrArg norm (sub_zero A)
        change dist A 0 < ε
        change ‖A‖ ≤ η * (2 * ρ) at hbound
        have hnorm_lt : ‖A‖ < ε :=
          lt_of_le_of_lt hbound hη_lt
        exact
          Eq.subst
            (motive := fun x : ℝ => x < ε)
            (Eq.symm hdist_norm)
            hnorm_lt))

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
  let H : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k
  let V : ℕ → ℂ := fun k =>
    Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k
  let Hsum : ℂ := ∑ k in Finset.range (m + 1), H k
  let Vsum : ℂ := ∑ k in Finset.range (m + 1), V k
  let Top : ℂ := Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m
  let Sample : ℂ := Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m
  let GraphH : ℂ := Complex.rightSemicircleGraphHorizontalIntegral f c ρ
  let GraphV : ℂ := Complex.rightSemicircleGraphVerticalIntegral f c ρ
  have hhorizontal_bound :
      ‖(Hsum + Top) - Sample‖
        ≤ η * (2 * ρ) :=
    Complex.norm_sum_rightSemicircleStaircaseHorizontal_sub_sampleSum_le
      f c hρ hcont
      m hη_nonneg hhorizontal
  have hvertical_bound :
      ‖Vsum - GraphV‖
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
      show
        (Complex.rightSemicircleAngleIntegral f c ρ -
            Complex.rightSemicircleGraphVerticalIntegral f c ρ) +
            Complex.rightSemicircleGraphVerticalIntegral f c ρ =
          Complex.rightSemicircleAngleIntegral f c ρ
      exact
        horizontal_add_vertical_eq_total
          (Complex.rightSemicircleAngleIntegral f c ρ)
          (Complex.rightSemicircleGraphVerticalIntegral f c ρ)
    exact htarget.symm
  have hdecomp :
      Complex.rightSemicirclePolygonalArcIntegral f c ρ m -
          Complex.rightSemicircleAngleIntegral f c ρ =
        (Hsum + Top - Sample) + (Sample - GraphH) + (Vsum - GraphV) := by
    show
      ((∑ k in Finset.range (m + 1), (H k + V k)) + Top) -
          Complex.rightSemicircleAngleIntegral f c ρ =
        (Hsum + Top - Sample) + (Sample - GraphH) + (Vsum - GraphV)
    have hsum_split :
        (∑ k in Finset.range (m + 1), (H k + V k)) = Hsum + Vsum :=
      Finset.sum_add_distrib
    exact
      Eq.trans
        (congrArg
          (fun z : ℂ =>
            (z + Top) -
              Complex.rightSemicircleAngleIntegral f c ρ)
          hsum_split)
        (Eq.subst
          (motive := fun angle : ℂ =>
            ((Hsum + Vsum) + Top) - angle =
              (Hsum + Top - Sample) + (Sample - GraphH) + (Vsum - GraphV))
          hangle.symm
          (polygonal_arc_error_decompose_additive
            Hsum Top Vsum Sample GraphH GraphV))
  have hdecomp_bound :
      ‖(Hsum + Top - Sample) + (Sample - GraphH) + (Vsum - GraphV)‖
        ≤ η * (6 * ρ) := by
    let A : ℂ := Hsum + Top - Sample
    let B : ℂ := Sample - GraphH
    let C : ℂ := Vsum - GraphV
    have hA : ‖A‖ ≤ η * (2 * ρ) := hhorizontal_bound
    have hB : ‖B‖ ≤ η * (2 * ρ) := hquadrature
    have hC : ‖C‖ ≤ η * (2 * ρ) := hvertical_bound
    have hnorm_three : ‖A + B + C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
      le_trans
        (norm_add_le (A + B) C)
        (add_le_add_right (norm_add_le A B) ‖C‖)
    calc
      ‖(Hsum + Top - Sample) + (Sample - GraphH) + (Vsum - GraphV)‖
          = ‖A + B + C‖ := rfl
      _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := hnorm_three
      _ ≤ η * (2 * ρ) + η * (2 * ρ) + η * (2 * ρ) := by
              exact add_le_add (add_le_add hA hB) hC
      _ ≤ η * (6 * ρ) := by
              exact three_two_radius_errors_le_six_radius_error hη_nonneg hρ.le
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ η * (6 * ρ))
      (Eq.symm hdecomp)
      hdecomp_bound

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
    show Complex.rightSemicircleAngleGrid ρ m 0 = -(Real.pi / 2)
    exact Complex.rightSemicircleAngleGrid_zero hρ m
  have hB : a (m + 1) = Real.pi / 2 := by
    show Complex.rightSemicircleAngleGrid ρ m (m + 1) = Real.pi / 2
    exact Complex.rightSemicircleAngleGrid_last hρ m
  have hD_cont : Continuous D := by
    show Continuous (fun θ : ℝ => ((-ρ * Real.sin θ : ℝ) : ℂ))
    exact
      Complex.continuous_ofReal.comp
        ((continuous_const : Continuous fun _ : ℝ => (-ρ)).mul Real.continuous_sin)
  have hint :
      ∀ k < m + 1, IntervalIntegrable G volume (a k) (a (k + 1)) := by
    intro k hk
    have hkmem : k ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr hk
    have hsubset :
        [[a k, a (k + 1)]] ⊆
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      show
        [[Complex.rightSemicircleAngleGrid ρ m k,
          Complex.rightSemicircleAngleGrid ρ m (k + 1)]] ⊆
          Set.Icc (-(Real.pi / 2)) (Real.pi / 2)
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
      have hconst_cont : Continuous (fun θ : ℝ => F (a k) * D θ) :=
        continuous_const.mul hD_cont
      exact hconst_cont.continuousOn.intervalIntegrable
    have hGcell :
        IntervalIntegrable G volume (a k) (a (k + 1)) := by
      exact hint k (Complex.staircase_cell_index_lt hk)
    have hchord :
        (((ρ * Real.cos (a (k + 1)) -
           ρ * Real.cos (a k) : ℝ) : ℂ)) =
          ∫ θ : ℝ in a k..a (k + 1), D θ := by
      show
        (((ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m (k + 1)) -
           ρ * Real.cos (Complex.rightSemicircleAngleGrid ρ m k) : ℝ) : ℂ)) =
          ∫ θ : ℝ in
            Complex.rightSemicircleAngleGrid ρ m k..
              Complex.rightSemicircleAngleGrid ρ m (k + 1),
            ((-ρ * Real.sin θ : ℝ) : ℂ)
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
            exact
              Eq.trans
                (congrArg
                  (fun z : ℂ =>
                    F (a k) * z -
                      ∫ θ : ℝ in a k..a (k + 1), G θ)
                  hchord)
                (congrArg
                  (fun z : ℂ =>
                    z - ∫ θ : ℝ in a k..a (k + 1), G θ)
                  (Eq.symm
                    (intervalIntegral.integral_const_mul
                      (r := F (a k))
                      (f := D)
                      (a := a k)
                      (b := a (k + 1)))))
      _ =
        ∫ θ : ℝ in a k..a (k + 1),
          (F (a k) * D θ - G θ) := by
            exact
              Eq.symm
                (intervalIntegral.integral_sub hconst hGcell)
      _ =
        ∫ θ : ℝ in a k..a (k + 1),
          (F (a k) - F θ) * D θ := by
            apply intervalIntegral.integral_congr
            intro θ _hθ
            show F (a k) * D θ - F θ * D θ =
              (F (a k) - F θ) * D θ
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
    have hle :
        ∀ θ ∈ Set.uIoc (a k) (a (k + 1)),
          ‖(F (a k) - F θ) * D θ‖ ≤ η * ρ := by
      intro θ hθ
      have hθcell : θ ∈ [[a k, a (k + 1)]] :=
        Set.uIoc_subset_uIcc hθ
      have hosc : ‖F (a k) - F θ‖ ≤ η := by
        show ‖F (Complex.rightSemicircleAngleGrid ρ m k) - F θ‖ ≤ η
        exact happrox k hk θ hθcell
      have hD : ‖D θ‖ ≤ ρ := by
        show ‖((-ρ * Real.sin θ : ℝ) : ℂ)‖ ≤ ρ
        have hnorm_real :
            ‖((-ρ * Real.sin θ : ℝ) : ℂ)‖ = |-ρ * Real.sin θ| :=
          Eq.trans
            (RCLike.norm_ofReal (K := ℂ) (-ρ * Real.sin θ))
            (Real.norm_eq_abs (-ρ * Real.sin θ))
        calc
          ‖((-ρ * Real.sin θ : ℝ) : ℂ)‖ = |-ρ * Real.sin θ| :=
            hnorm_real
          _ = ρ * |Real.sin θ| := by
            exact
              Eq.trans
                (abs_mul (-ρ) (Real.sin θ))
                (congrArg
                  (fun x : ℝ => x * |Real.sin θ|)
                  (Eq.trans (abs_neg ρ) (abs_of_nonneg hρ.le)))
          _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) hρ.le
          _ = ρ := mul_one ρ
      calc
        ‖(F (a k) - F θ) * D θ‖
            = ‖F (a k) - F θ‖ * ‖D θ‖ := norm_mul _ _
        _ ≤ η * ρ := mul_le_mul hosc hD (norm_nonneg _) hη_nonneg
    exact
      Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ η * ρ * |a (k + 1) - a k|)
        (Eq.symm (hterm k hk))
        (intervalIntegral.norm_integral_le_of_norm_le_const hle)
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
    exact
      Eq.trans
        (congrArg
          (fun z : ℂ =>
            (∑ k in Finset.range (m + 1),
              F (a k) *
                (((ρ * Real.cos (a (k + 1)) -
                   ρ * Real.cos (a k) : ℝ) : ℂ))) - z)
          hintegral_split)
        (Finset.sum_sub_distrib.symm)
  have hsum_lengths :
      (∑ k in Finset.range (m + 1), |a (k + 1) - a k|) = Real.pi := by
    have hmono : ∀ k < m + 1, a k ≤ a (k + 1) := by
      intro k hk
      show
        Complex.rightSemicircleAngleGrid ρ m k ≤
          Complex.rightSemicircleAngleGrid ρ m (k + 1)
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
      exact
        Eq.trans
          (Finset.sum_congr rfl (fun k hk => habs k hk))
          (Eq.trans
            (Finset.sum_congr rfl
              (fun k _hk =>
                calc
                  a (k + 1) - a k = -a k - -a (k + 1) := by
                    exact
                      Eq.symm
                        (Eq.trans
                          (sub_neg_eq_add (-a k) (a (k + 1)))
                          (Eq.trans
                            (add_comm (-a k) (a (k + 1)))
                            (Eq.symm (sub_eq_add_neg (a (k + 1)) (a k)))))
                  _ = (fun i => -a i) k - (fun i => -a i) (k + 1) := by
                    rfl))
            (Eq.trans
              (Finset.sum_range_sub' (fun i => -a i) (m + 1))
              (calc
                (fun i => -a i) 0 - (fun i => -a i) (m + 1) =
                    -a 0 - -a (m + 1) := by
                  rfl
                _ = a (m + 1) - a 0 := by
                  exact
                    Eq.trans
                      (sub_neg_eq_add (-a 0) (a (m + 1)))
                      (Eq.trans
                        (add_comm (-a 0) (a (m + 1)))
                        (Eq.symm (sub_eq_add_neg (a (m + 1)) (a 0)))))))
    exact
      Eq.trans htel
        (Eq.trans
          (congrArg₂ HSub.hSub hB hA)
          pi_div_two_sub_neg_pi_div_two)
  have hdecomp_bound :
      ‖∑ k in Finset.range (m + 1),
          (F (a k) *
              (((ρ * Real.cos (a (k + 1)) -
                 ρ * Real.cos (a k) : ℝ) : ℂ)) -
            ∫ θ : ℝ in a k..a (k + 1), G θ)‖
        ≤ η * (Real.pi * ρ) := by
    calc
      ‖∑ k in Finset.range (m + 1),
          (F (a k) *
              (((ρ * Real.cos (a (k + 1)) -
                 ρ * Real.cos (a k) : ℝ) : ℂ)) -
            ∫ θ : ℝ in a k..a (k + 1), G θ)‖
        ≤
          ∑ k in Finset.range (m + 1),
            ‖F (a k) *
                (((ρ * Real.cos (a (k + 1)) -
                   ρ * Real.cos (a k) : ℝ) : ℂ)) -
              ∫ θ : ℝ in a k..a (k + 1), G θ‖ := by
          exact norm_sum_le _ _
      _ ≤
          ∑ k in Finset.range (m + 1),
            η * ρ *
              |a (k + 1) - a k| := by
          exact Finset.sum_le_sum hcell_bound
      _ =
          η * ρ *
            ∑ k in Finset.range (m + 1),
              |a (k + 1) - a k| := by
          exact
            finset_sum_two_const_mul_eq_mul_mul_sum
              (Finset.range (m + 1))
              η
              ρ
              (fun k =>
                |a (k + 1) - a k|)
      _ = η * ρ * Real.pi := by
          exact
            congrArg
              (fun x : ℝ => η * ρ * x)
              hsum_lengths
      _ = η * (Real.pi * ρ) := by
          exact eta_mul_radius_mul_pi_eq_eta_mul_pi_mul_radius η ρ
  exact
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ η * (Real.pi * ρ))
      (Eq.symm hdecomp)
      hdecomp_bound

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
  exact Metric.tendsto_atTop.mpr (fun ε hε => by
  have hπρ_pos : 0 < Real.pi * ρ :=
    mul_pos Real.pi_pos hρ
  let η : ℝ := (ε / 2) / (Real.pi * ρ)
  have hε_half_pos : 0 < ε / 2 :=
    half_pos hε
  have hη_pos : 0 < η := div_pos hε_half_pos hπρ_pos
  have hη_nonneg : 0 ≤ η := le_of_lt hη_pos
  have hF_uniform :
      UniformContinuousOn F
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hF
  let ⟨δ, hδ, hδ_modulus⟩ :=
    Metric.uniformContinuousOn_iff.mp hF_uniform η hη_pos
  have hmesh :
      ∀ᶠ m : ℕ in atTop,
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
            Complex.rightSemicircleAngleGrid ρ m k| < δ :=
    Complex.eventually_rightSemicircleAngleGrid_cell_length_lt hρ hδ
  match eventually_atTop.mp hmesh with
  | Exists.intro N hN =>
  exact Exists.intro N (fun m hmN => by
    have hm :
        ∀ k ∈ Finset.range (m + 1),
          |Complex.rightSemicircleAngleGrid ρ m (k + 1) -
            Complex.rightSemicircleAngleGrid ρ m k| < δ :=
      hN m hmN
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
        exact Set.mem_uIcc.mp hθ
      have hdist_grid :
          dist θ (Complex.rightSemicircleAngleGrid ρ m k) <
            δ := by
        have hdist_abs :
            dist θ (Complex.rightSemicircleAngleGrid ρ m k) =
              |θ - Complex.rightSemicircleAngleGrid ρ m k| :=
          Real.dist_eq θ (Complex.rightSemicircleAngleGrid ρ m k)
        apply
          Eq.subst
            (motive := fun x : ℝ => x < δ)
            (Eq.symm hdist_abs)
        match hcell with
        | Or.inl hcell =>
          have hnonneg :
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
                  (Finset.mem_range.mp hk)))
          have habs_theta :
              |θ - Complex.rightSemicircleAngleGrid ρ m k| =
                θ - Complex.rightSemicircleAngleGrid ρ m k :=
            abs_of_nonneg hnonneg
          have hgrid_lt :
              Complex.rightSemicircleAngleGrid ρ m (k + 1) -
                  Complex.rightSemicircleAngleGrid ρ m k < δ :=
            Eq.subst
              (motive := fun x : ℝ => x < δ)
              hgrid_abs
              (hm k hk)
          exact
            Eq.subst
              (motive := fun x : ℝ => x < δ)
              (Eq.symm habs_theta)
              (lt_of_le_of_lt hle hgrid_lt)
        | Or.inr hcell =>
          have hnonneg :
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
                (Finset.mem_range.mp hk))
          have hzero :
              Complex.rightSemicircleAngleGrid ρ m k - θ = 0 := by
            exact le_antisymm (le_trans hle hreverse_nonpos) hnonneg
          have habs_theta :
              |θ - Complex.rightSemicircleAngleGrid ρ m k| =
                Complex.rightSemicircleAngleGrid ρ m k - θ :=
            Eq.trans
              (abs_sub_comm θ (Complex.rightSemicircleAngleGrid ρ m k))
              (abs_of_nonneg hnonneg)
          exact
            Eq.subst
              (motive := fun x : ℝ => x < δ)
              (Eq.symm (Eq.trans habs_theta hzero))
              hδ
      have hclose : dist (F θ) (F (Complex.rightSemicircleAngleGrid ρ m k)) < η :=
        hδ_modulus θ hθ_Icc
          (Complex.rightSemicircleAngleGrid ρ m k) htag_Icc
          hdist_grid
      have hnorm :
          ‖F θ - F (Complex.rightSemicircleAngleGrid ρ m k)‖ < η := by
        exact
          (dist_eq_norm (F θ) (F (Complex.rightSemicircleAngleGrid ρ m k))) ▸
            hclose
      have hnorm_symm :
          ‖F (Complex.rightSemicircleAngleGrid ρ m k) - F θ‖ < η := by
        have hsub :
            F (Complex.rightSemicircleAngleGrid ρ m k) - F θ =
              -(F θ - F (Complex.rightSemicircleAngleGrid ρ m k)) :=
          Eq.symm (neg_sub (F θ) (F (Complex.rightSemicircleAngleGrid ρ m k)))
        exact
          Eq.subst
            (motive := fun z : ℂ => ‖z‖ < η)
            (Eq.symm hsub)
            (Eq.subst
              (motive := fun x : ℝ => x < η)
              (Eq.symm (norm_neg (F θ - F (Complex.rightSemicircleAngleGrid ρ m k))))
              hnorm)
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
    have hη_eq : η * (Real.pi * ρ) = ε / 2 := by
      show ((ε / 2) / (Real.pi * ρ)) * (Real.pi * ρ) = ε / 2
      exact div_mul_cancel_of_pos_right hπρ_pos
    have hη_lt : η * (Real.pi * ρ) < ε :=
      Eq.subst
        (motive := fun x : ℝ => x < ε)
        (Eq.symm hη_eq)
        (half_lt_self hε)
    exact lt_of_le_of_lt hbound hη_lt))

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
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
        atTop
        (𝓝
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)))) :=
    Tendsto.congr'
      (Filter.Eventually.of_forall
        (fun m : ℕ =>
          Eq.symm
            (Complex.rightSemicircleGraphHorizontalSampleSum_eq_angleChordSum
              f c hρ m)))
      hchord
  have htarget :
      Complex.rightSemicircleGraphHorizontalIntegral f c ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          F θ * (((-ρ * Real.sin θ : ℝ) : ℂ)) :=
    Complex.rightSemicircleGraphHorizontalIntegral_eq_angle_dx
      f c hρ hcont
  exact htarget.symm ▸ hsample

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
  have hsum_limit :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m +
            (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
              Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m))
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun m : ℕ =>
            Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m +
              (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
                Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m))
          atTop
          (𝓝 z))
      (add_zero (Complex.rightSemicircleGraphHorizontalIntegral f c ρ))
      hsum
  exact
    Tendsto.congr'
      (Filter.Eventually.of_forall
        (fun m : ℕ =>
          add_sub_right_cancel'
            (Complex.rightSemicircleGraphHorizontalSampleSum f c ρ m)
            (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)))
      hsum_limit

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
  exact Metric.tendsto_atTop.mpr (fun ε hε => by
  have hsixρ_pos : 0 < 6 * ρ :=
    real_six_mul_pos_of_pos hρ
  let η : ℝ := (ε / 2) / (6 * ρ)
  have hε_half_pos : 0 < ε / 2 :=
    half_pos hε
  have hη_pos : 0 < η := div_pos hε_half_pos hsixρ_pos
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
    exact
      eventually_atTop.mpr
        (match hmetric with
        | Exists.intro N hN =>
          Exists.intro N (fun m hmN => by
            have hm := hN m hmN
            show
              ‖Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m -
                Complex.rightSemicircleGraphHorizontalIntegral f c ρ‖ ≤
                  η * (2 * ρ)
            exact
              (dist_eq_norm
                (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
                (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) ▸
                le_of_lt hm))
  match
    eventually_atTop.mp
      (hhorizontal_event.and (hvertical_event.and hquadrature_event))
  with
  | Exists.intro N hN =>
    exact Exists.intro N (fun m hmN => by
      have hevents := hN m hmN
      have hhorizontal := hevents.1
      have hvertical := hevents.2.1
      have hquadrature := hevents.2.2
      have hbound :
          ‖Complex.rightSemicirclePolygonalArcIntegral f c ρ m -
            Complex.rightSemicircleAngleIntegral f c ρ‖ ≤ η * (6 * ρ) :=
        Complex.norm_rightSemicircleStaircaseArcIntegral_sub_angleIntegral_le_pathApprox
          f c hρ hcont m hη_nonneg hhorizontal hvertical hquadrature
      have hη_eq : η * (6 * ρ) = ε / 2 := by
        show ((ε / 2) / (6 * ρ)) * (6 * ρ) = ε / 2
        exact div_mul_cancel_of_pos_right hsixρ_pos
      have hη_lt : η * (6 * ρ) < ε :=
        Eq.subst
          (motive := fun x : ℝ => x < ε)
          (Eq.symm hη_eq)
          (half_lt_self hε)
      exact lt_of_le_of_lt hbound hη_lt))

end

end LFunctions
end Boundary
