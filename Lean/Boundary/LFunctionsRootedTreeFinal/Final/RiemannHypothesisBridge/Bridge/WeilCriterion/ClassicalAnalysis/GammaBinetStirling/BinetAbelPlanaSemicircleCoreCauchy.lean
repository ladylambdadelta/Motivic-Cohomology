import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleApproximation

/-!
# Curvilinear semicircle core Cauchy-Goursat layer

This file owns the right and left deleted half-rectangle core boundary theorems
used by finite Abel-Plana cap-collar and punctured-boundary accounting.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The lower chord of the right indentation lies in the right core collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_bottom_mem
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    {x : ℝ}
    (hx : x ∈ [[c.re, c.re + a]]) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have him_mem :
      c.im - ρ ∈ [[c.im - ρ, c.im + ρ]] := by
    exact left_mem_uIcc
  have hnot_ball :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have him_abs :
        ρ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ := by
      have him_eq :
          ((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im =
            -ρ := by
        simp [sub_im]
      calc
        ρ = |(-ρ : ℝ)| := by rw [abs_of_nonneg hρ.le, abs_neg]
        _ = |((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im| := by
          rw [him_eq]
        _ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ :=
          Complex.abs_im_le_norm _
    have hdist_lt : ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hball
    exact not_lt_of_ge him_abs hdist_lt
  exact ⟨⟨hx, him_mem⟩, hnot_ball⟩

/-- The upper chord of the right indentation lies in the right core collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_top_mem
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    {x : ℝ}
    (hx : x ∈ [[c.re, c.re + a]]) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  have him_mem :
      c.im + ρ ∈ [[c.im - ρ, c.im + ρ]] := by
    exact right_mem_uIcc
  have hnot_ball :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have him_abs :
        ρ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ := by
      have him_eq :
          ((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im =
            ρ := by
        simp [sub_im]
      calc
        ρ = |ρ| := by rw [abs_of_nonneg hρ.le]
        _ = |((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im| := by
          rw [him_eq]
        _ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ :=
          Complex.abs_im_le_norm _
    have hdist_lt : ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hball
    exact not_lt_of_ge him_abs hdist_lt
  exact ⟨⟨hx, him_mem⟩, hnot_ball⟩

/-- The safe vertical side of the right indentation lies in the right core
collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_vertical_mem
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    {y : ℝ}
    (hy : y ∈ [[c.im - ρ, c.im + ρ]]) :
    (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have hre_mem :
      c.re + a ∈ [[c.re, c.re + a]] := by
    exact right_mem_uIcc
  have hnot_ball :
      (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have hre_abs :
        ρ ≤ ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ := by
      have hre_eq :
          ((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re =
            a := by
        simp [sub_re]
      calc
        ρ ≤ a := hρa
        _ = |a| := by rw [abs_of_nonneg ha]
        _ = |((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re| := by
          rw [hre_eq]
        _ ≤ ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ :=
          Complex.abs_re_le_norm _
    have hdist_lt : ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hball
    exact not_lt_of_ge hre_abs hdist_lt
  exact ⟨⟨hre_mem, hy⟩, hnot_ball⟩

/-- The right semicircular indentation arc lies in the right core collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_arc_mem
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    {θ : ℝ}
    (hθ : θ ∈ [[-(Real.pi / 2), Real.pi / 2]]) :
    c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have hθIcc : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [Set.uIcc_of_le (by linarith [Real.pi_pos] :
      -(Real.pi / 2) ≤ Real.pi / 2)] using hθ
  have hre :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        ρ * Real.cos θ := by
    simp [Complex.exp_re, mul_re]
  have him :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        ρ * Real.sin θ := by
    simp [Complex.exp_im, mul_im]
  have hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθIcc
  have hre_mem :
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re ∈
        [[c.re, c.re + a]] := by
    rw [add_re, hre]
    have hleft : c.re ≤ c.re + ρ * Real.cos θ := by
      nlinarith [mul_nonneg hρ.le hcos_nonneg]
    have hright : c.re + ρ * Real.cos θ ≤ c.re + a := by
      have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have hρcos_le : ρ * Real.cos θ ≤ ρ :=
        mul_le_of_le_one_right hρ.le hcos_le
      linarith
    simpa [Set.uIcc_of_le (by linarith : c.re ≤ c.re + a)] using
      And.intro hleft hright
  have hsin_abs : |Real.sin θ| ≤ 1 :=
    abs_le.mpr (Real.sin_mem_Icc θ)
  have him_mem :
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im ∈
        [[c.im - ρ, c.im + ρ]] := by
    rw [add_im, him]
    have him_abs : |ρ * Real.sin θ| ≤ ρ := by
      calc
        |ρ * Real.sin θ| = ρ * |Real.sin θ| := by
          rw [abs_mul, abs_of_nonneg hρ.le]
        _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρ.le
        _ = ρ := mul_one ρ
    have hb := abs_le.mp him_abs
    have hleft : c.im - ρ ≤ c.im + ρ * Real.sin θ := by linarith
    have hright : c.im + ρ * Real.sin θ ≤ c.im + ρ := by linarith
    simpa [Set.uIcc_of_le (by linarith : c.im - ρ ≤ c.im + ρ)] using
      And.intro hleft hright
  have hnot_ball :
      c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∉
        Metric.ball c ρ := by
    have hz_eq :
        c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
          circleMap c ρ θ := by
      dsimp [circleMap]
      ring
    rw [hz_eq]
    exact circleMap_not_mem_ball c ρ θ
  exact ⟨⟨hre_mem, him_mem⟩, hnot_ball⟩

/-- The closed rectangular tail after the tangent line `Re z = c.re + ρ`
lies in the deleted right core. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_rectangularTail_subset_core
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ) :
    ([[c.re + ρ, c.re + a]] ×ℂ [[c.im - ρ, c.im + ρ]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  intro z hz
  have ha : 0 ≤ a := le_trans hρ.le hρa
  have htail_order : c.re + ρ ≤ c.re + a := by linarith
  have hcore_order : c.re ≤ c.re + a := by linarith
  have hzdata := Complex.mem_reProdIm.mp hz
  have hzre_tail : z.re ∈ Set.Icc (c.re + ρ) (c.re + a) := by
    simpa [Set.uIcc_of_le htail_order] using hzdata.1
  have hzre_core : z.re ∈ [[c.re, c.re + a]] := by
    have hleft : c.re ≤ z.re := by linarith [hzre_tail.1, hρ.le]
    have hright : z.re ≤ c.re + a := hzre_tail.2
    simpa [Set.uIcc_of_le hcore_order] using And.intro hleft hright
  have hnot_ball : z ∉ Metric.ball c ρ := by
    intro hball
    have hre_abs_le_norm : |(z - c).re| ≤ ‖z - c‖ :=
      Complex.abs_re_le_norm (z - c)
    have hre_eq : (z - c).re = z.re - c.re := by
      simp [sub_re]
    have hre_ge : ρ ≤ |(z - c).re| := by
      rw [hre_eq]
      have hnonneg : 0 ≤ z.re - c.re := by linarith [hzre_tail.1, hρ.le]
      have hle : ρ ≤ z.re - c.re := by linarith [hzre_tail.1]
      simpa [abs_of_nonneg hnonneg] using hle
    have hnorm_ge : ρ ≤ ‖z - c‖ := le_trans hre_ge hre_abs_le_norm
    have hnorm_lt : ‖z - c‖ < ρ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hball
    exact not_lt_of_ge hnorm_ge hnorm_lt
  exact ⟨⟨hzre_core, hzdata.2⟩, hnot_ball⟩

/-- Cauchy-Goursat on the ordinary rectangular tail of the right deleted core. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_rectangularTailBoundary_eq_zero
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
    Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ = 0 := by
  let z₀ : ℂ := (((c.re + ρ : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))
  let z₁ : ℂ := (((c.re + a : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
    dsimp [z₀, z₁]
    simpa using
      Complex.rightHalfRectangleDeletedDiskCore_rectangularTail_subset_core
        c a hρa hρ
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral,
    z₀, z₁, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hcauchy

/-- The four right-indentation boundary integrands are interval-integrable.

This is the measure-theoretic side condition for any later boundary evaluation
or collar-decomposition argument; it is independent of the topological
Cauchy-Goursat proof. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_boundary_intervalIntegrable
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        volume c.re (c.re + a) ∧
      IntervalIntegrable
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        volume c.re (c.re + a) ∧
      IntervalIntegrable
        (fun y : ℝ =>
          Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (c.im - ρ) (c.im + ρ) ∧
      IntervalIntegrable
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        volume (-(Real.pi / 2)) (Real.pi / 2) := by
  have hbottom_cont :
      ContinuousOn
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
        [[c.re, c.re + a]] := by
    have hparam :
        ContinuousOn
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]] :=
      (continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        MapsTo
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro x hx
      exact Complex.rightHalfRectangleDeletedDiskCore_bottom_mem c a hρa hρ hx
    exact hcont.comp_continuousOn hparam hmem
  have htop_cont :
      ContinuousOn
        (fun x : ℝ =>
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
        [[c.re, c.re + a]] := by
    have hparam :
        ContinuousOn
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]] :=
      (continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        MapsTo
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro x hx
      exact Complex.rightHalfRectangleDeletedDiskCore_top_mem c a hρa hρ hx
    exact hcont.comp_continuousOn hparam hmem
  have hvertical_cont :
      ContinuousOn
        (fun y : ℝ =>
          Complex.I *
            f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        [[c.im - ρ, c.im + ρ]] := by
    have hparam :
        ContinuousOn
          (fun y : ℝ =>
            (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          [[c.im - ρ, c.im + ρ]] :=
      (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
    have hmem :
        MapsTo
          (fun y : ℝ =>
            (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          [[c.im - ρ, c.im + ρ]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro y hy
      exact Complex.rightHalfRectangleDeletedDiskCore_vertical_mem c a hρa hρ hy
    exact continuousOn_const.mul (hcont.comp_continuousOn hparam hmem)
  have harc_cont :
      ContinuousOn
        (fun θ : ℝ =>
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ))))
        [[-(Real.pi / 2), Real.pi / 2]] := by
    have hparam_cont :
        ContinuousOn
          (fun θ : ℝ =>
            c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          [[-(Real.pi / 2), Real.pi / 2]] :=
      (continuous_const.add
        (continuous_const.mul
          (Complex.continuous_exp.comp
            (continuous_const.mul continuous_ofReal)))).continuousOn
    have hmem :
        MapsTo
          (fun θ : ℝ =>
            c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
          [[-(Real.pi / 2), Real.pi / 2]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro θ hθ
      exact Complex.rightHalfRectangleDeletedDiskCore_arc_mem c a hρa hρ hθ
    have hf_cont :
        ContinuousOn
          (fun θ : ℝ =>
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
          [[-(Real.pi / 2), Real.pi / 2]] :=
      hcont.comp_continuousOn hparam_cont hmem
    have htangent_cont :
        ContinuousOn
          (fun θ : ℝ =>
            Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ)))
          [[-(Real.pi / 2), Real.pi / 2]] :=
      ((continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul continuous_ofReal))).continuousOn
    exact hf_cont.mul htangent_cont
  exact
    ⟨hbottom_cont.intervalIntegrable,
      htop_cont.intervalIntegrable,
      hvertical_cont.intervalIntegrable,
      harc_cont.intervalIntegrable⟩

/-- If the ambient height strictly dominates the deletion radius, the right core
collar lies in the corresponding taller right collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρT : ρ < |T|) :
    Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ ⊆
      Complex.rightHalfRectangleDeletedDiskDomain c T a ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have him_left :
      c.im - ρ ∈ [[c.im - T, c.im + T]] := by
    by_cases hT : 0 ≤ T
    · have hρ_le_T : ρ ≤ T := by
        exact le_of_lt (by simpa [abs_of_nonneg hT] using hρT)
      have horder : c.im - T ≤ c.im + T := by linarith
      have hleft : c.im - T ≤ c.im - ρ := by linarith
      have hright : c.im - ρ ≤ c.im + T := by linarith
      simpa [Set.uIcc_of_le horder] using And.intro hleft hright
    · have hT_lt : T < 0 := lt_of_not_ge hT
      have hT_le : T ≤ 0 := le_of_lt hT_lt
      have hρ_le_negT : ρ ≤ -T := by
        exact le_of_lt (by simpa [abs_of_neg hT_lt] using hρT)
      have horder : c.im + T ≤ c.im - T := by linarith
      have hleft : c.im + T ≤ c.im - ρ := by linarith
      have hright : c.im - ρ ≤ c.im - T := by linarith
      simpa [Set.uIcc_comm, Set.uIcc_of_le horder] using And.intro hleft hright
  have him_right :
      c.im + ρ ∈ [[c.im - T, c.im + T]] := by
    by_cases hT : 0 ≤ T
    · have hρ_le_T : ρ ≤ T := by
        exact le_of_lt (by simpa [abs_of_nonneg hT] using hρT)
      have horder : c.im - T ≤ c.im + T := by linarith
      have hleft : c.im - T ≤ c.im + ρ := by linarith
      have hright : c.im + ρ ≤ c.im + T := by linarith
      simpa [Set.uIcc_of_le horder] using And.intro hleft hright
    · have hT_lt : T < 0 := lt_of_not_ge hT
      have hT_le : T ≤ 0 := le_of_lt hT_lt
      have hρ_le_negT : ρ ≤ -T := by
        exact le_of_lt (by simpa [abs_of_neg hT_lt] using hρT)
      have horder : c.im + T ≤ c.im - T := by linarith
      have hleft : c.im + T ≤ c.im + ρ := by linarith
      have hright : c.im + ρ ≤ c.im - T := by linarith
      simpa [Set.uIcc_comm, Set.uIcc_of_le horder] using And.intro hleft hright
  have him_tall : z.im ∈ [[c.im - T, c.im + T]] :=
    uIcc_subset_uIcc him_left him_right him
  exact ⟨⟨hre, him_tall⟩, hnot_ball⟩

/-- If the ambient height strictly dominates the deletion radius, the left core
collar lies in the corresponding taller left collar. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρT : ρ < |T|) :
    Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ ⊆
      Complex.leftHalfRectangleDeletedDiskDomain c T a ρ := by
  intro z hz
  rcases hz with ⟨hbox, hnot_ball⟩
  rcases hbox with ⟨hre, him⟩
  have him_left :
      c.im - ρ ∈ [[c.im - T, c.im + T]] := by
    by_cases hT : 0 ≤ T
    · have hρ_le_T : ρ ≤ T := by
        exact le_of_lt (by simpa [abs_of_nonneg hT] using hρT)
      have horder : c.im - T ≤ c.im + T := by linarith
      have hleft : c.im - T ≤ c.im - ρ := by linarith
      have hright : c.im - ρ ≤ c.im + T := by linarith
      simpa [Set.uIcc_of_le horder] using And.intro hleft hright
    · have hT_lt : T < 0 := lt_of_not_ge hT
      have hT_le : T ≤ 0 := le_of_lt hT_lt
      have hρ_le_negT : ρ ≤ -T := by
        exact le_of_lt (by simpa [abs_of_neg hT_lt] using hρT)
      have horder : c.im + T ≤ c.im - T := by linarith
      have hleft : c.im + T ≤ c.im - ρ := by linarith
      have hright : c.im - ρ ≤ c.im - T := by linarith
      simpa [Set.uIcc_comm, Set.uIcc_of_le horder] using And.intro hleft hright
  have him_right :
      c.im + ρ ∈ [[c.im - T, c.im + T]] := by
    by_cases hT : 0 ≤ T
    · have hρ_le_T : ρ ≤ T := by
        exact le_of_lt (by simpa [abs_of_nonneg hT] using hρT)
      have horder : c.im - T ≤ c.im + T := by linarith
      have hleft : c.im - T ≤ c.im + ρ := by linarith
      have hright : c.im + ρ ≤ c.im + T := by linarith
      simpa [Set.uIcc_of_le horder] using And.intro hleft hright
    · have hT_lt : T < 0 := lt_of_not_ge hT
      have hT_le : T ≤ 0 := le_of_lt hT_lt
      have hρ_le_negT : ρ ≤ -T := by
        exact le_of_lt (by simpa [abs_of_neg hT_lt] using hρT)
      have horder : c.im + T ≤ c.im - T := by linarith
      have hleft : c.im + T ≤ c.im + ρ := by linarith
      have hright : c.im + ρ ≤ c.im - T := by linarith
      simpa [Set.uIcc_comm, Set.uIcc_of_le horder] using And.intro hleft hright
  have him_tall : z.im ∈ [[c.im - T, c.im + T]] :=
    uIcc_subset_uIcc him_left him_right him
  exact ⟨⟨hre, him_tall⟩, hnot_ball⟩

/-- Curvilinear Cauchy-Goursat theorem for the right half-rectangle collar
outside a deleted disk.

This is the exact classical topological input: the two horizontal chords, the
safe vertical chord, and the right semicircle are the positively oriented
boundary of the right half-rectangle with the disk removed. -/
theorem Complex.rightHalfRectangleDeletedDiskCurvilinearCauchyGoursat
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
    Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero_owner
      f c a hρa hρ hcont hdiff

/-- Core Cauchy-Goursat theorem for the right half-rectangle collar outside a
deleted disk.

This wrapper keeps the local Abel-Plana naming stable while the owner theorem
above records the actual analytic input. -/
theorem Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
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
    Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 :=
  Complex.rightHalfRectangleDeletedDiskCurvilinearCauchyGoursat
    f c a hρa hρ hcont hdiff

/-- Core Cauchy-Goursat theorem for the left half-rectangle collar outside a
deleted disk. -/
theorem Complex.leftHalfRectangleDeletedDiskCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ)) :
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ = 0 := by
  have hcont_turn :
      ContinuousOn (Complex.halfTurnPullback c f)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :=
    Complex.continuousOn_halfTurnPullback_rightCore_of_leftCore
      f c a ρ (le_trans hρ.le hρa) hρ.le hcont
  have hdiff_turn :
      DifferentiableOn ℂ (Complex.halfTurnPullback c f)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) :=
    Complex.differentiableOn_halfTurnPullback_rightCore_of_leftCore
      f c a ρ (le_trans hρ.le hρa) hρ.le hdiff
  calc
    Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral f c a ρ =
        -Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral
          (Complex.halfTurnPullback c f) c a ρ :=
      Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral_eq_neg_halfTurn_right
        f c a ρ
    _ = 0 :=
      neg_eq_zero.mpr
        (Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
          (Complex.halfTurnPullback c f) c a hρa hρ hcont_turn hdiff_turn)

/-- Generic Cauchy-Goursat theorem for the right half-rectangle collar outside a
deleted disk.

This is the reusable local curvilinear contour theorem.  Its boundary is the
two lower/upper chord segments, the safe vertical chord at `c.re + a`, and the
counterclockwise right semicircle with deleted-boundary orientation subtracted. -/
theorem Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hρT : ρ < |T|)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskDomain c T a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskDomain c T a ρ)) :
    (∫ x : ℝ in c.re..(c.re + a),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in c.re..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_core :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hcont.mono
      (Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρT)
  have hdiff_core :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hdiff.mono
      (Complex.rightHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρT)
  simpa [Complex.rightHalfRectangleDeletedDiskCoreBoundaryIntegral] using
    (Complex.rightHalfRectangleDeletedDiskCoreBoundary_eq_zero
      f c a hρa hρ hcont_core hdiff_core)

/-- Generic Cauchy-Goursat theorem for the left half-rectangle collar outside a
deleted disk.

This is the reflected local curvilinear contour theorem.  Its boundary is the
two lower/upper chord segments, the safe vertical chord at `c.re - a`, and the
counterclockwise left semicircle with deleted-boundary orientation subtracted. -/
theorem Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    (T a : ℝ)
    {ρ : ℝ}
    (hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    (hρT : ρ < |T|)
    (hcont :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskDomain c T a ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskDomain c T a ρ)) :
    (∫ x : ℝ in (c.re - a)..c.re,
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
        -(∫ x : ℝ in (c.re - a)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re - a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_core :
      ContinuousOn f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hcont.mono
      (Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρT)
  have hdiff_core :
      DifferentiableOn ℂ f
        (Complex.leftHalfRectangleDeletedDiskCoreDomain c a ρ) := by
    exact hdiff.mono
      (Complex.leftHalfRectangleDeletedDiskCoreDomain_subset_heightDomain
        c T a hρT)
  simpa [Complex.leftHalfRectangleDeletedDiskCoreBoundaryIntegral] using
    (Complex.leftHalfRectangleDeletedDiskCoreBoundary_eq_zero
      f c a hρa hρ hcont_core hdiff_core)

end

end LFunctions
end Boundary
