import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseGeometry

/-!
# Right-semicircle graph layer for finite-height Abel-Plana collars

This file owns the basic graph parametrization of the right semicircle, its
continuity on the closed height interval, and the first vertical
interval-integrability consequence.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Interval integrability descends to a subinterval whose endpoints both lie
in the original unordered interval. -/
theorem Complex.intervalIntegrable_of_mem_uIcc
    {F : ℝ → ℂ}
    {a b c d : ℝ}
    (hF : IntervalIntegrable F volume a b)
    (hc : c ∈ [[a, b]])
    (hd : d ∈ [[a, b]]) :
    IntervalIntegrable F volume c d := by
  exact hF.mono_set (Set.uIcc_subset_uIcc hc hd)

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
      c.re + Complex.rightSemicircleGraphRe ρ y :=
  Complex.ofReal_add_I_mul_ofReal_re
    (c.re + Complex.rightSemicircleGraphRe ρ y)
    (c.im + y)

/-- Imaginary coordinate of the right-semicircle graph point. -/
theorem Complex.rightSemicircleGraphPoint_im
    (c : ℂ)
    (ρ y : ℝ) :
    (Complex.rightSemicircleGraphPoint c ρ y).im = c.im + y :=
  Complex.ofReal_add_I_mul_ofReal_im
    (c.re + Complex.rightSemicircleGraphRe ρ y)
    (c.im + y)

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
    exact
      Eq.trans
        (Complex.ofReal_add_I_mul_ofReal_im (c.re + x) (c.im + y))
        (Eq.symm (Complex.rightSemicircleGraphPoint_im c ρ y))
  have hdist : dist z₁ z₂ = dist z₁.re z₂.re :=
    Complex.dist_of_im_eq him
  have hz₁_re : z₁.re = c.re + x := by
    exact Complex.ofReal_add_I_mul_ofReal_re (c.re + x) (c.im + y)
  have hz₂_re : z₂.re = c.re + Complex.rightSemicircleGraphRe ρ y := by
    exact Complex.rightSemicircleGraphPoint_re c ρ y
  have hsub :
      z₁.re - z₂.re = x - Complex.rightSemicircleGraphRe ρ y := by
    calc
      z₁.re - z₂.re =
          (c.re + x) - z₂.re :=
        congrArg (fun r : ℝ => r - z₂.re) hz₁_re
      _ = (c.re + x) - (c.re + Complex.rightSemicircleGraphRe ρ y) :=
        congrArg (fun r : ℝ => (c.re + x) - r) hz₂_re
      _ = x - Complex.rightSemicircleGraphRe ρ y :=
        add_sub_add_left_eq_sub x (Complex.rightSemicircleGraphRe ρ y) c.re
  calc
    dist
      ((((c.re + x : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ))))
      (Complex.rightSemicircleGraphPoint c ρ y)
        = dist z₁ z₂ := rfl
    _ = dist z₁.re z₂.re := hdist
    _ = |z₁.re - z₂.re| := Real.dist_eq z₁.re z₂.re
    _ = |x - Complex.rightSemicircleGraphRe ρ y| :=
      congrArg abs hsub

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
    have hy_abs_radius : |y| ≤ |ρ| :=
      Eq.subst
        (motive := fun r : ℝ => |y| ≤ r)
        (Eq.symm (abs_of_nonneg hρ.le))
        hy_abs
    have hy_sq : y ^ 2 ≤ ρ ^ 2 := sq_le_sq.mpr hy_abs_radius
    exact sub_nonneg.mpr hy_sq
  have hinner :
      ContinuousOn (fun y : ℝ => ρ ^ 2 - y ^ 2) (Set.Icc (-ρ) ρ) :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  show
    ContinuousOn
      (fun y : ℝ => Real.sqrt (ρ ^ 2 - y ^ 2))
      (Set.Icc (-ρ) ρ)
  exact Real.continuous_sqrt.comp_continuousOn hinner

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
  show
    ContinuousOn
      (fun y : ℝ =>
        (((c.re + Complex.rightSemicircleGraphRe ρ y : ℝ) : ℂ) +
          Complex.I * (((c.im + y : ℝ) : ℂ))))
      (Set.Icc (-ρ) ρ)
  have hreal_part :
      ContinuousOn
        (fun y : ℝ => ((c.re + Complex.rightSemicircleGraphRe ρ y : ℝ) : ℂ))
        (Set.Icc (-ρ) ρ) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.continuousOn).add hgraph_cont)
  have him_part :
      ContinuousOn
        (fun y : ℝ => ((c.im + y : ℝ) : ℂ))
        (Set.Icc (-ρ) ρ) :=
    Complex.continuous_ofReal.comp_continuousOn
      ((continuous_const.add continuous_id).continuousOn)
  exact
    hreal_part.add
      (continuous_const.continuousOn.mul him_part)

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
      Set.MapsTo
        (fun y : ℝ => Complex.rightSemicircleGraphPoint c ρ y)
        (Set.Icc (-ρ) ρ)
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    exact Complex.rightSemicircleGraphPoint_mem_core_self c hρ hy
  exact ContinuousOn.comp hcont hparam hmaps

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
  let ⟨B₀, hB₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbounded
  let B : ℝ := max B₀ 0
  have hB_nonneg : 0 ≤ B := le_max_right B₀ 0
  exact
    ⟨B, hB_nonneg,
      fun y hy =>
        have hmem :
            f (Complex.rightSemicircleGraphPoint c ρ y) ∈
              (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y)) ''
                Set.Icc (-ρ) ρ := ⟨y, hy, rfl⟩
        have hball := hB₀ hmem
        have hnorm_le_B₀ :
            ‖f (Complex.rightSemicircleGraphPoint c ρ y)‖ ≤ B₀ := by
          have hdist :
              dist (f (Complex.rightSemicircleGraphPoint c ρ y)) 0 ≤ B₀ :=
            Metric.mem_closedBall.mp hball
          exact (dist_zero_right (f (Complex.rightSemicircleGraphPoint c ρ y))) ▸ hdist
        le_trans hnorm_le_B₀ (le_max_left B₀ 0)⟩

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
  have hprobe_Icc :
      ContinuousOn
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
        (Set.Icc (-ρ) ρ) :=
    Complex.continuousOn_rightSemicircleGraphVerticalIntegrand
      f c hρ hcont
  have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
    Set.uIcc_of_le (Complex.neg_radius_le_radius hρ.le)
  have hprobe_uIcc :
      ContinuousOn
        (fun y : ℝ => f (Complex.rightSemicircleGraphPoint c ρ y))
        [[-ρ, ρ]] :=
    huIcc ▸ hprobe_Icc
  exact hprobe_uIcc.intervalIntegrable

/-- Real part of the exponential on the `Iθ` parametrized circle. -/
theorem Complex.exp_I_mul_ofReal_re
    (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ))).re = Real.cos θ := by
  calc
    (Complex.exp (Complex.I * (θ : ℂ))).re =
        (Complex.exp ((θ : ℂ) * Complex.I)).re := by
      exact congrArg (fun z : ℂ => (Complex.exp z).re)
        (mul_comm Complex.I (θ : ℂ))
    _ = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

/-- Imaginary part of the exponential on the `Iθ` parametrized circle. -/
theorem Complex.exp_I_mul_ofReal_im
    (θ : ℝ) :
    (Complex.exp (Complex.I * (θ : ℂ))).im = Real.sin θ := by
  calc
    (Complex.exp (Complex.I * (θ : ℂ))).im =
        (Complex.exp ((θ : ℂ) * Complex.I)).im := by
      exact congrArg (fun z : ℂ => (Complex.exp z).im)
        (mul_comm Complex.I (θ : ℂ))
    _ = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

/-- Real coordinate of the right semicircle radius vector. -/
theorem Complex.realRadius_exp_I_mul_re
    (ρ θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
      ρ * Real.cos θ := by
  calc
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        ρ * (Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact Complex.re_ofReal_mul ρ (Complex.exp (Complex.I * (θ : ℂ)))
    _ = ρ * Real.cos θ := by
      exact congrArg (fun u : ℝ => ρ * u)
        (Complex.exp_I_mul_ofReal_re θ)

/-- Imaginary coordinate of the right semicircle radius vector. -/
theorem Complex.realRadius_exp_I_mul_im
    (ρ θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
      ρ * Real.sin θ := by
  calc
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        ρ * (Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.im_ofReal_mul ρ (Complex.exp (Complex.I * (θ : ℂ)))
    _ = ρ * Real.sin θ := by
      exact congrArg (fun u : ℝ => ρ * u)
        (Complex.exp_I_mul_ofReal_im θ)

/-- Real coordinate of a center plus a semicircle radius vector. -/
theorem Complex.add_realRadius_exp_I_mul_re
    (c : ℂ)
    (ρ θ : ℝ) :
    (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
      c.re + ρ * Real.cos θ := by
  calc
    (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        c.re + ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re := by
      exact Complex.add_re c ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    _ = c.re + ρ * Real.cos θ := by
      exact congrArg (fun u : ℝ => c.re + u)
        (Complex.realRadius_exp_I_mul_re ρ θ)

/-- Imaginary coordinate of a center plus a semicircle radius vector. -/
theorem Complex.add_realRadius_exp_I_mul_im
    (c : ℂ)
    (ρ θ : ℝ) :
    (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
      c.im + ρ * Real.sin θ := by
  calc
    (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        c.im + ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im := by
      exact Complex.add_im c ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))
    _ = c.im + ρ * Real.sin θ := by
      exact congrArg (fun u : ℝ => c.im + u)
        (Complex.realRadius_exp_I_mul_im ρ θ)

end

end LFunctions
end Boundary
