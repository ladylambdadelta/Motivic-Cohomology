import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaRectangularCollars
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleGraph
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicirclePathConvergence

/-!
# Right semicircle core tail layer

This file owns the right-core coordinate, rectangular-tail Cauchy-Goursat, and
boundary-integrability facts used by the semicircular core boundary wrapper.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory
open scoped Topology Interval

/-- The standard right semicircle angle interval is ordered. -/
theorem Real.neg_half_pi_le_half_pi :
    -(Real.pi / 2) ≤ Real.pi / 2 := by
  exact neg_le_self (div_nonneg Real.pi_pos.le zero_le_two)

/-- Adding a nonnegative width gives an ordered real interval. -/
theorem Real.le_add_of_nonneg_width
    (x a : ℝ)
    (ha : 0 ≤ a) :
    x ≤ x + a :=
  le_add_of_nonneg_right ha

/-- Translating a width inequality preserves the endpoint order. -/
theorem Real.add_width_le_add_width
    (x : ℝ)
    {ρ a : ℝ}
    (hρa : ρ ≤ a) :
    x + ρ ≤ x + a :=
  add_le_add_left hρa x

/-- The right semicircle parameterization agrees with mathlib's `circleMap`. -/
theorem Complex.rightSemicircle_param_eq_circleMap
    (c : ℂ)
    (ρ θ : ℝ) :
    c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
      circleMap c ρ θ := by
  calc
    c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
        c + (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
      exact congrArg
        (fun z : ℂ => c + (ρ : ℂ) * Complex.exp z)
        (mul_comm Complex.I (θ : ℂ))
    _ = circleMap c ρ θ := rfl

/-- Imaginary coordinate of a lower horizontal chord relative to its center. -/
theorem Complex.lowerHorizontalChord_sub_center_im
    (c : ℂ)
    (ρ x : ℝ) :
    ((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im =
      -ρ := by
  calc
    ((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im =
        (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)).im - c.im := by
      exact Complex.sub_im
        (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) c
    _ = (((x : ℝ) : ℂ).im +
          (Complex.I * ((c.im - ρ : ℝ) : ℂ)).im) - c.im := by
      exact congrArg (fun u : ℝ => u - c.im)
        (Complex.add_im ((x : ℝ) : ℂ)
          (Complex.I * ((c.im - ρ : ℝ) : ℂ)))
    _ = (0 + (Complex.I * ((c.im - ρ : ℝ) : ℂ)).im) - c.im := by
      exact congrArg
        (fun u : ℝ => (u + (Complex.I * ((c.im - ρ : ℝ) : ℂ)).im) - c.im)
        (Complex.ofReal_im x)
    _ = (0 + ((c.im - ρ : ℝ) : ℂ).re) - c.im := by
      exact congrArg (fun u : ℝ => (0 + u) - c.im)
        (Complex.I_mul_im ((c.im - ρ : ℝ) : ℂ))
    _ = (0 + (c.im - ρ)) - c.im := by
      exact congrArg (fun u : ℝ => (0 + u) - c.im)
        (Complex.ofReal_re (c.im - ρ))
    _ = (c.im - ρ) - c.im := by
      exact congrArg (fun u : ℝ => u - c.im) (zero_add (c.im - ρ))
    _ = -ρ := sub_sub_cancel_left c.im ρ

/-- Imaginary coordinate of an upper horizontal chord relative to its center. -/
theorem Complex.upperHorizontalChord_sub_center_im
    (c : ℂ)
    (ρ x : ℝ) :
    ((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im =
      ρ := by
  calc
    ((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im =
        (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)).im - c.im := by
      exact Complex.sub_im
        (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) c
    _ = (((x : ℝ) : ℂ).im +
          (Complex.I * ((c.im + ρ : ℝ) : ℂ)).im) - c.im := by
      exact congrArg (fun u : ℝ => u - c.im)
        (Complex.add_im ((x : ℝ) : ℂ)
          (Complex.I * ((c.im + ρ : ℝ) : ℂ)))
    _ = (0 + (Complex.I * ((c.im + ρ : ℝ) : ℂ)).im) - c.im := by
      exact congrArg
        (fun u : ℝ => (u + (Complex.I * ((c.im + ρ : ℝ) : ℂ)).im) - c.im)
        (Complex.ofReal_im x)
    _ = (0 + ((c.im + ρ : ℝ) : ℂ).re) - c.im := by
      exact congrArg (fun u : ℝ => (0 + u) - c.im)
        (Complex.I_mul_im ((c.im + ρ : ℝ) : ℂ))
    _ = (0 + (c.im + ρ)) - c.im := by
      exact congrArg (fun u : ℝ => (0 + u) - c.im)
        (Complex.ofReal_re (c.im + ρ))
    _ = (c.im + ρ) - c.im := by
      exact congrArg (fun u : ℝ => u - c.im) (zero_add (c.im + ρ))
    _ = ρ := add_sub_cancel_left c.im ρ

/-- Real coordinate of the safe vertical chord relative to its center. -/
theorem Complex.safeVerticalChord_sub_center_re
    (c : ℂ)
    (a y : ℝ) :
    ((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re = a := by
  calc
    ((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re =
        (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)).re - c.re := by
      exact Complex.sub_re
        (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) c
    _ = (((c.re + a : ℝ) : ℂ).re + (Complex.I * (y : ℂ)).re) - c.re := by
      exact congrArg (fun u : ℝ => u - c.re)
        (Complex.add_re (((c.re + a : ℝ) : ℂ)) (Complex.I * (y : ℂ)))
    _ = ((c.re + a) + (Complex.I * (y : ℂ)).re) - c.re := by
      exact congrArg (fun u : ℝ => (u + (Complex.I * (y : ℂ)).re) - c.re)
        (Complex.ofReal_re (c.re + a))
    _ = ((c.re + a) + -(y : ℂ).im) - c.re := by
      exact congrArg (fun u : ℝ => ((c.re + a) + u) - c.re)
        (Complex.I_mul_re (y : ℂ))
    _ = ((c.re + a) + -0) - c.re := by
      exact congrArg (fun u : ℝ => ((c.re + a) + -u) - c.re)
        (Complex.ofReal_im y)
    _ = ((c.re + a) + 0) - c.re := by
      exact congrArg (fun u : ℝ => ((c.re + a) + u) - c.re) (neg_zero)
    _ = (c.re + a) - c.re := by
      exact congrArg (fun u : ℝ => u - c.re) (add_zero (c.re + a))
    _ = a := add_sub_cancel_left c.re a

/-- Real coordinate of a difference. -/
theorem Complex.sub_center_re
    (z c : ℂ) :
    (z - c).re = z.re - c.re :=
  Complex.sub_re z c

/-- Real part of a complex number is bounded by its norm. -/
theorem Complex.rightCoreTail_abs_re_le_norm
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  exact (Complex.norm_eq_abs z).symm ▸ Complex.abs_re_le_abs z

/-- Imaginary part of a complex number is bounded by its norm. -/
theorem Complex.rightCoreTail_abs_im_le_norm
    (z : ℂ) :
    |z.im| ≤ ‖z‖ := by
  exact (Complex.norm_eq_abs z).symm ▸ Complex.abs_im_le_abs z

/-- Lower horizontal chord real coordinate. -/
theorem Complex.lowerHorizontalChord_re
    (c : ℂ)
    (ρ x : ℝ) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)).re = x :=
  Complex.ofReal_add_I_mul_ofReal_re x (c.im - ρ)

/-- Lower horizontal chord imaginary coordinate. -/
theorem Complex.lowerHorizontalChord_im
    (c : ℂ)
    (ρ x : ℝ) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)).im = c.im - ρ :=
  Complex.ofReal_add_I_mul_ofReal_im x (c.im - ρ)

/-- Upper horizontal chord real coordinate. -/
theorem Complex.upperHorizontalChord_re
    (c : ℂ)
    (ρ x : ℝ) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)).re = x :=
  Complex.ofReal_add_I_mul_ofReal_re x (c.im + ρ)

/-- Upper horizontal chord imaginary coordinate. -/
theorem Complex.upperHorizontalChord_im
    (c : ℂ)
    (ρ x : ℝ) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)).im = c.im + ρ :=
  Complex.ofReal_add_I_mul_ofReal_im x (c.im + ρ)

/-- Right vertical chord real coordinate. -/
theorem Complex.safeVerticalChord_re
    (c : ℂ)
    (a y : ℝ) :
    (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = c.re + a :=
  Complex.ofReal_add_I_mul_ofReal_re (c.re + a) y

/-- Right vertical chord imaginary coordinate. -/
theorem Complex.safeVerticalChord_im
    (c : ℂ)
    (a y : ℝ) :
    (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)).im = y :=
  Complex.ofReal_add_I_mul_ofReal_im (c.re + a) y

/-- Transport a lower bound across equality with an absolute value. -/
theorem Real.le_abs_of_le_of_eq
    {a x y : ℝ}
    (hxy : x = y)
    (hle : a ≤ y) :
    a ≤ x :=
  Eq.subst
    (motive := fun u : ℝ => a ≤ u)
    (Eq.symm hxy)
    hle

/-- Membership in an ordered interval transports to the unordered interval. -/
theorem Set.mem_uIcc_of_mem_Icc_of_le
    {x a b : ℝ}
    (hab : a ≤ b)
    (hx : x ∈ Set.Icc a b) :
    x ∈ [[a, b]] := by
  exact Eq.subst
    (motive := fun s : Set ℝ => x ∈ s)
    (Eq.symm (Set.uIcc_of_le hab))
    hx

/-- Membership in an unordered interval transports to the ordered interval when
the endpoints are known to be ordered. -/
theorem Set.mem_Icc_of_mem_uIcc_of_le
    {x a b : ℝ}
    (hab : a ≤ b)
    (hx : x ∈ [[a, b]]) :
    x ∈ Set.Icc a b := by
  exact Eq.subst
    (motive := fun s : Set ℝ => x ∈ s)
    (Set.uIcc_of_le hab)
    hx

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
    exact Set.left_mem_uIcc
  have hnot_ball :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have him_abs :
        ρ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ := by
      have him_eq :
          ((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im =
            -ρ := by
        exact Complex.lowerHorizontalChord_sub_center_im c ρ x
      calc
        ρ = |(-ρ : ℝ)| := by
          exact Eq.symm ((abs_neg ρ).trans (abs_of_nonneg hρ.le))
        _ = |((((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c).im| := by
          exact congrArg abs (Eq.symm him_eq)
        _ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ :=
          Complex.rightCoreTail_abs_im_le_norm _
    have hdist_lt : ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)) - c‖ < ρ := by
      exact Complex.norm_sub_lt_radius_of_mem_ball hball
    exact not_lt_of_ge him_abs hdist_lt
  have hre_mem :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)).re ∈
        [[c.re, c.re + a]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.re, c.re + a]])
      (Eq.symm (Complex.lowerHorizontalChord_re c ρ x))
      hx
  have him_mem' :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)).im ∈
        [[c.im - ρ, c.im + ρ]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.im - ρ, c.im + ρ]])
      (Eq.symm (Complex.lowerHorizontalChord_im c ρ x))
      him_mem
  exact ⟨⟨hre_mem, him_mem'⟩, hnot_ball⟩

/-- The upper chord of the right indentation lies in the right core collar. -/
theorem Complex.rightHalfRectangleDeletedDiskCore_top_mem
    (c : ℂ)
    (a : ℝ)
    {ρ : ℝ}
    (_hρa : ρ ≤ a)
    (hρ : 0 < ρ)
    {x : ℝ}
    (hx : x ∈ [[c.re, c.re + a]]) :
    (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ := by
  have him_mem :
      c.im + ρ ∈ [[c.im - ρ, c.im + ρ]] := by
    exact Set.right_mem_uIcc
  have hnot_ball :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have him_abs :
        ρ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ := by
      have him_eq :
          ((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im =
            ρ := by
        exact Complex.upperHorizontalChord_sub_center_im c ρ x
      calc
        ρ = |ρ| := Eq.symm (abs_of_nonneg hρ.le)
        _ = |((((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c).im| := by
          exact congrArg abs (Eq.symm him_eq)
        _ ≤ ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ :=
          Complex.rightCoreTail_abs_im_le_norm _
    have hdist_lt : ‖(((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) - c‖ < ρ := by
      exact Complex.norm_sub_lt_radius_of_mem_ball hball
    exact not_lt_of_ge him_abs hdist_lt
  have hre_mem :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)).re ∈
        [[c.re, c.re + a]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.re, c.re + a]])
      (Eq.symm (Complex.upperHorizontalChord_re c ρ x))
      hx
  have him_mem' :
      (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)).im ∈
        [[c.im - ρ, c.im + ρ]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.im - ρ, c.im + ρ]])
      (Eq.symm (Complex.upperHorizontalChord_im c ρ x))
      him_mem
  exact ⟨⟨hre_mem, him_mem'⟩, hnot_ball⟩

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
    exact Set.right_mem_uIcc
  have hnot_ball :
      (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∉
        Metric.ball c ρ := by
    intro hball
    have hre_abs :
        ρ ≤ ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ := by
      have hre_eq :
          ((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re =
            a := by
        exact Complex.safeVerticalChord_sub_center_re c a y
      calc
        ρ ≤ a := hρa
        _ = |a| := Eq.symm (abs_of_nonneg ha)
        _ = |((((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c).re| := by
          exact congrArg abs (Eq.symm hre_eq)
        _ ≤ ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ :=
          Complex.rightCoreTail_abs_re_le_norm _
    have hdist_lt : ‖(((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)) - c‖ < ρ := by
      exact Complex.norm_sub_lt_radius_of_mem_ball hball
    exact not_lt_of_ge hre_abs hdist_lt
  have hre_mem' :
      (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)).re ∈
        [[c.re, c.re + a]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.re, c.re + a]])
      (Eq.symm (Complex.safeVerticalChord_re c a y))
      hre_mem
  have him_mem :
      (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)).im ∈
        [[c.im - ρ, c.im + ρ]] :=
    Eq.subst
      (motive := fun u : ℝ => u ∈ [[c.im - ρ, c.im + ρ]])
      (Eq.symm (Complex.safeVerticalChord_im c a y))
      hy
  exact ⟨⟨hre_mem', him_mem⟩, hnot_ball⟩

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
    exact Set.mem_Icc_of_mem_uIcc_of_le
      Real.neg_half_pi_le_half_pi hθ
  have hre :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
        ρ * Real.cos θ := by
    exact Complex.realRadius_exp_I_mul_re ρ θ
  have him :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
        ρ * Real.sin θ := by
    exact Complex.realRadius_exp_I_mul_im ρ θ
  have hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθIcc
  have hre_mem :
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re ∈
        [[c.re, c.re + a]] := by
    have hre_eq :
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re =
          c.re + ρ * Real.cos θ :=
      Complex.add_realRadius_exp_I_mul_re c ρ θ
    have hρcos_nonneg : 0 ≤ ρ * Real.cos θ :=
      mul_nonneg hρ.le hcos_nonneg
    have hleft : c.re ≤ c.re + ρ * Real.cos θ :=
      Real.le_add_of_nonneg_width c.re (ρ * Real.cos θ) hρcos_nonneg
    have hright : c.re + ρ * Real.cos θ ≤ c.re + a := by
      have hcos_le : Real.cos θ ≤ 1 := Real.cos_le_one θ
      have hρcos_le : ρ * Real.cos θ ≤ ρ :=
        mul_le_of_le_one_right hρ.le hcos_le
      exact le_trans (add_le_add_left hρcos_le c.re)
        (Real.add_width_le_add_width c.re hρa)
    have hordered_mem :
        c.re + ρ * Real.cos θ ∈ Set.Icc c.re (c.re + a) :=
      And.intro hleft hright
    have hunordered_mem :
        c.re + ρ * Real.cos θ ∈ [[c.re, c.re + a]] :=
      Set.mem_uIcc_of_mem_Icc_of_le
        (Real.le_add_of_nonneg_width c.re a ha)
        hordered_mem
    exact Eq.subst
      (motive := fun x : ℝ => x ∈ [[c.re, c.re + a]])
      (Eq.symm hre_eq)
      hunordered_mem
  have hsin_abs : |Real.sin θ| ≤ 1 :=
    abs_le.mpr (Real.sin_mem_Icc θ)
  have him_mem :
      (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im ∈
        [[c.im - ρ, c.im + ρ]] := by
    have him_eq :
        (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im =
          c.im + ρ * Real.sin θ :=
      Complex.add_realRadius_exp_I_mul_im c ρ θ
    have him_abs : |ρ * Real.sin θ| ≤ ρ := by
      calc
        |ρ * Real.sin θ| = |ρ| * |Real.sin θ| :=
          abs_mul ρ (Real.sin θ)
        _ = ρ * |Real.sin θ| := by
          exact congrArg (fun u : ℝ => u * |Real.sin θ|)
            (abs_of_nonneg hρ.le)
        _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρ.le
        _ = ρ := mul_one ρ
    have hb := abs_le.mp him_abs
    have hleft : c.im - ρ ≤ c.im + ρ * Real.sin θ := by
      exact (sub_eq_add_neg c.im ρ) ▸ add_le_add_left hb.1 c.im
    have hright : c.im + ρ * Real.sin θ ≤ c.im + ρ :=
      add_le_add_left hb.2 c.im
    have him_order : c.im - ρ ≤ c.im + ρ := by
      exact (sub_eq_add_neg c.im ρ) ▸
        add_le_add_left (neg_le_self hρ.le) c.im
    have hordered_mem :
        c.im + ρ * Real.sin θ ∈ Set.Icc (c.im - ρ) (c.im + ρ) :=
      And.intro hleft hright
    have hunordered_mem :
        c.im + ρ * Real.sin θ ∈ [[c.im - ρ, c.im + ρ]] :=
      Set.mem_uIcc_of_mem_Icc_of_le him_order hordered_mem
    exact Eq.subst
      (motive := fun y : ℝ => y ∈ [[c.im - ρ, c.im + ρ]])
      (Eq.symm him_eq)
      hunordered_mem
  have hnot_ball :
      c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) ∉
        Metric.ball c ρ := by
    have hz_eq :
        c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) =
          circleMap c ρ θ := by
      exact Complex.rightSemicircle_param_eq_circleMap c ρ θ
    exact Eq.subst
      (motive := fun z : ℂ => z ∉ Metric.ball c ρ)
      (Eq.symm hz_eq)
      (circleMap_not_mem_ball c ρ θ)
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
  have htail_order : c.re + ρ ≤ c.re + a :=
    Real.add_width_le_add_width c.re hρa
  have hcore_order : c.re ≤ c.re + a :=
    Real.le_add_of_nonneg_width c.re a ha
  have hzdata := Complex.mem_reProdIm.mp hz
  have hzre_tail : z.re ∈ Set.Icc (c.re + ρ) (c.re + a) := by
    exact Set.mem_Icc_of_mem_uIcc_of_le htail_order hzdata.1
  have hzre_core : z.re ∈ [[c.re, c.re + a]] := by
    have hleft : c.re ≤ z.re :=
      le_trans (Real.le_add_of_nonneg_width c.re ρ hρ.le) hzre_tail.1
    have hright : z.re ≤ c.re + a := hzre_tail.2
    exact Set.mem_uIcc_of_mem_Icc_of_le hcore_order
      (And.intro hleft hright)
  have hnot_ball : z ∉ Metric.ball c ρ := by
    intro hball
    have hre_abs_le_norm : |(z - c).re| ≤ ‖z - c‖ :=
      Complex.rightCoreTail_abs_re_le_norm (z - c)
    have hre_eq : (z - c).re = z.re - c.re := by
      exact Complex.sub_center_re z c
    have hre_ge : ρ ≤ |(z - c).re| := by
      have hcle : c.re ≤ z.re :=
        le_trans (Real.le_add_of_nonneg_width c.re ρ hρ.le) hzre_tail.1
      have hnonneg : 0 ≤ z.re - c.re :=
        sub_nonneg.mpr hcle
      have hρ_add : ρ + c.re ≤ z.re := by
        exact (add_comm c.re ρ) ▸ hzre_tail.1
      have hle : ρ ≤ z.re - c.re :=
        (le_sub_iff_add_le).mpr hρ_add
      have hdiff_abs : z.re - c.re = |z.re - c.re| :=
        Eq.symm (abs_of_nonneg hnonneg)
      have htarget_abs : |(z - c).re| = |z.re - c.re| :=
        congrArg abs hre_eq
      have hle_abs : ρ ≤ |z.re - c.re| :=
        Real.le_abs_of_le_of_eq (Eq.symm hdiff_abs) hle
      exact Eq.subst
        (motive := fun u : ℝ => ρ ≤ u)
        (Eq.symm htarget_abs)
        hle_abs
    have hnorm_ge : ρ ≤ ‖z - c‖ := le_trans hre_ge hre_abs_le_norm
    have hnorm_lt : ‖z - c‖ < ρ := by
      exact Complex.norm_sub_lt_radius_of_mem_ball hball
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
    intro z hz
    have hzdata := Complex.mem_reProdIm.mp hz
    have hz₀_re : z₀.re = c.re + ρ :=
      Complex.ofReal_add_I_mul_ofReal_re (c.re + ρ) (c.im - ρ)
    have hz₁_re : z₁.re = c.re + a :=
      Complex.ofReal_add_I_mul_ofReal_re (c.re + a) (c.im + ρ)
    have hz₀_im : z₀.im = c.im - ρ :=
      Complex.ofReal_add_I_mul_ofReal_im (c.re + ρ) (c.im - ρ)
    have hz₁_im : z₁.im = c.im + ρ :=
      Complex.ofReal_add_I_mul_ofReal_im (c.re + a) (c.im + ρ)
    have hre_interval_eq :
        [[z₀.re, z₁.re]] = [[c.re + ρ, c.re + a]] :=
      congrArg₂ Set.uIcc hz₀_re hz₁_re
    have him_interval_eq :
        [[z₀.im, z₁.im]] = [[c.im - ρ, c.im + ρ]] :=
      congrArg₂ Set.uIcc hz₀_im hz₁_im
    have hre_mem : z.re ∈ [[c.re + ρ, c.re + a]] :=
      Eq.subst
        (motive := fun s : Set ℝ => z.re ∈ s)
        hre_interval_eq
        hzdata.1
    have him_mem : z.im ∈ [[c.im - ρ, c.im + ρ]] :=
      Eq.subst
        (motive := fun s : Set ℝ => z.im ∈ s)
        him_interval_eq
        hzdata.2
    exact
      Complex.rightHalfRectangleDeletedDiskCore_rectangularTail_subset_core
        c a hρa hρ
        (Complex.mem_reProdIm.mpr ⟨hre_mem, him_mem⟩)
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
  calc
    Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral f c a ρ =
      (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in (c.re + ρ)..(c.re + a),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) :=
      Complex.rightHalfRectangleDeletedDiskCoreRectangularTailBoundaryIntegral_unfold
        f c a ρ
    _ =
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) := by
      have hz₀_re : z₀.re = c.re + ρ :=
        Complex.ofReal_add_I_mul_ofReal_re (c.re + ρ) (c.im - ρ)
      have hz₁_re : z₁.re = c.re + a :=
        Complex.ofReal_add_I_mul_ofReal_re (c.re + a) (c.im + ρ)
      have hz₀_im : z₀.im = c.im - ρ :=
        Complex.ofReal_add_I_mul_ofReal_im (c.re + ρ) (c.im - ρ)
      have hz₁_im : z₁.im = c.im + ρ :=
        Complex.ofReal_add_I_mul_ofReal_im (c.re + a) (c.im + ρ)
      let B₀ : ℝ → ℂ := fun x =>
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))
      let B₁ : ℝ → ℂ := fun x =>
        f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)
      let T₀ : ℝ → ℂ := fun x =>
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
      let T₁ : ℝ → ℂ := fun x =>
        f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)
      let R₀ : ℝ → ℂ := fun y =>
        f (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ))
      let R₁ : ℝ → ℂ := fun y =>
        f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)
      let L₀ : ℝ → ℂ := fun y =>
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
      let L₁ : ℝ → ℂ := fun y =>
        f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)
      have hB_same :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), B₀ x) =
            ∫ x : ℝ in (c.re + ρ)..(c.re + a), B₁ x :=
        intervalIntegral.integral_congr
          (fun x _hx =>
            congrArg f
              (congrArg
                (fun u : ℂ => (x : ℂ) + u)
                (Eq.trans
                  (Complex.ofReal_mul_I_eq_I_mul_ofReal (c.im - ρ)).symm
                  (congrArg (fun u : ℝ => (u : ℂ) * Complex.I)
                    (Eq.symm hz₀_im)))))
      have hB_left :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), B₁ x) =
            ∫ x : ℝ in z₀.re..(c.re + a), B₁ x :=
        congrArg
          (fun u : ℝ => ∫ x : ℝ in u..(c.re + a), B₁ x)
          (Eq.symm hz₀_re)
      have hB_right :
          (∫ x : ℝ in z₀.re..(c.re + a), B₁ x) =
            ∫ x : ℝ in z₀.re..z₁.re, B₁ x :=
        congrArg
          (fun u : ℝ => ∫ x : ℝ in z₀.re..u, B₁ x)
          (Eq.symm hz₁_re)
      have hB :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), B₀ x) =
            ∫ x : ℝ in z₀.re..z₁.re, B₁ x :=
        Eq.trans hB_same (Eq.trans hB_left hB_right)
      have hT_same :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), T₀ x) =
            ∫ x : ℝ in (c.re + ρ)..(c.re + a), T₁ x :=
        intervalIntegral.integral_congr
          (fun x _hx =>
            congrArg f
              (congrArg
                (fun u : ℂ => (x : ℂ) + u)
                (Eq.trans
                  (Complex.ofReal_mul_I_eq_I_mul_ofReal (c.im + ρ)).symm
                  (congrArg (fun u : ℝ => (u : ℂ) * Complex.I)
                    (Eq.symm hz₁_im)))))
      have hT_left :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), T₁ x) =
            ∫ x : ℝ in z₀.re..(c.re + a), T₁ x :=
        congrArg
          (fun u : ℝ => ∫ x : ℝ in u..(c.re + a), T₁ x)
          (Eq.symm hz₀_re)
      have hT_right :
          (∫ x : ℝ in z₀.re..(c.re + a), T₁ x) =
            ∫ x : ℝ in z₀.re..z₁.re, T₁ x :=
        congrArg
          (fun u : ℝ => ∫ x : ℝ in z₀.re..u, T₁ x)
          (Eq.symm hz₁_re)
      have hT :
          (∫ x : ℝ in (c.re + ρ)..(c.re + a), T₀ x) =
            ∫ x : ℝ in z₀.re..z₁.re, T₁ x :=
        Eq.trans hT_same (Eq.trans hT_left hT_right)
      have hR_same :
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), R₀ y) =
            ∫ y : ℝ in (c.im - ρ)..(c.im + ρ), R₁ y :=
        intervalIntegral.integral_congr
          (fun y _hy =>
            congrArg f
              (congrArg₂ HAdd.hAdd
                (congrArg (fun u : ℝ => (u : ℂ)) (Eq.symm hz₁_re))
                (Complex.ofReal_mul_I_eq_I_mul_ofReal y).symm))
      have hR_left :
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), R₁ y) =
            ∫ y : ℝ in z₀.im..(c.im + ρ), R₁ y :=
        congrArg
          (fun u : ℝ => ∫ y : ℝ in u..(c.im + ρ), R₁ y)
          (Eq.symm hz₀_im)
      have hR_right :
          (∫ y : ℝ in z₀.im..(c.im + ρ), R₁ y) =
            ∫ y : ℝ in z₀.im..z₁.im, R₁ y :=
        congrArg
          (fun u : ℝ => ∫ y : ℝ in z₀.im..u, R₁ y)
          (Eq.symm hz₁_im)
      have hR :
          Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), R₀ y) =
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, R₁ y) :=
        Eq.trans
          (congrArg (fun u : ℂ => Complex.I * u)
            (Eq.trans hR_same (Eq.trans hR_left hR_right)))
          rfl
      have hL_same :
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), L₀ y) =
            ∫ y : ℝ in (c.im - ρ)..(c.im + ρ), L₁ y :=
        intervalIntegral.integral_congr
          (fun y _hy =>
            congrArg f
              (congrArg₂ HAdd.hAdd
                (congrArg (fun u : ℝ => (u : ℂ)) (Eq.symm hz₀_re))
                (Complex.ofReal_mul_I_eq_I_mul_ofReal y).symm))
      have hL_left :
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), L₁ y) =
            ∫ y : ℝ in z₀.im..(c.im + ρ), L₁ y :=
        congrArg
          (fun u : ℝ => ∫ y : ℝ in u..(c.im + ρ), L₁ y)
          (Eq.symm hz₀_im)
      have hL_right :
          (∫ y : ℝ in z₀.im..(c.im + ρ), L₁ y) =
            ∫ y : ℝ in z₀.im..z₁.im, L₁ y :=
        congrArg
          (fun u : ℝ => ∫ y : ℝ in z₀.im..u, L₁ y)
          (Eq.symm hz₁_im)
      have hL :
          Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ), L₀ y) =
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, L₁ y) :=
        Eq.trans
          (congrArg (fun u : ℂ => Complex.I * u)
            (Eq.trans hL_same (Eq.trans hL_left hL_right)))
          rfl
      exact
        congrArg₂ HSub.hSub
          (congrArg₂ HAdd.hAdd
            (congrArg₂ HSub.hSub hB hT)
            hR)
          hL
    _ = 0 :=
      hcauchy

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
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        Set.MapsTo
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro x hx
      exact Complex.rightHalfRectangleDeletedDiskCore_bottom_mem c a hρa hρ hx
    exact ContinuousOn.comp hcont hparam hmem
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
      (Complex.continuous_ofReal.add continuous_const).continuousOn
    have hmem :
        Set.MapsTo
          (fun x : ℝ =>
            (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
          [[c.re, c.re + a]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro x hx
      exact Complex.rightHalfRectangleDeletedDiskCore_top_mem c a hρa hρ hx
    exact ContinuousOn.comp hcont hparam hmem
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
      (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hmem :
        Set.MapsTo
          (fun y : ℝ =>
            (((c.re + a : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          [[c.im - ρ, c.im + ρ]]
          (Complex.rightHalfRectangleDeletedDiskCoreDomain c a ρ) := by
      intro y hy
      exact Complex.rightHalfRectangleDeletedDiskCore_vertical_mem c a hρa hρ hy
    exact continuousOn_const.mul (ContinuousOn.comp hcont hparam hmem)
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
            (continuous_const.mul Complex.continuous_ofReal)))).continuousOn
    have hmem :
        Set.MapsTo
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
      ContinuousOn.comp hcont hparam_cont hmem
    have htangent_cont :
        ContinuousOn
          (fun θ : ℝ =>
            Complex.I * (ρ : ℂ) *
              Complex.exp (Complex.I * (θ : ℂ)))
          [[-(Real.pi / 2), Real.pi / 2]] :=
      ((continuous_const.mul continuous_const).mul
        (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))).continuousOn
    exact hf_cont.mul htangent_cont
  exact
    ⟨hbottom_cont.intervalIntegrable,
      htop_cont.intervalIntegrable,
      hvertical_cont.intervalIntegrable,
      harc_cont.intervalIntegrable⟩

end

end LFunctions
end Boundary
