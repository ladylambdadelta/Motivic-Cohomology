import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.ArctanBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMajorant

/-!
# Pointwise bounds for the Binet arctangent kernel

This file owns the elementary pointwise estimates for the arctangent kernel in
Binet's second formula.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Rewriting the lower split kernel majorant into constant-times-majorant
form. -/
theorem Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_eq
    (t : ℝ)
    (r : ℝ) :
    (2 * (t / r)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
      (2 / r) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  ring

/-- Norm of the Binet exponential denominator agrees with the positive real
denominator. -/
theorem Complex.binetSecondFormula_exp_denominator_norm_eq
    (t : ℝ) :
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
      ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
  calc
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        ‖((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ)‖ := by
      simp [Complex.ofReal_exp, Complex.ofReal_sub]
    _ = ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
      simp [Complex.normSq, Real.norm_eq_abs]

/-- Norm of the Binet arctangent argument. -/
theorem Complex.norm_real_div_eq_real_norm_div
    (t : ℝ)
    (w : ℂ) :
    ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ := by
  calc
    ‖(t : ℂ) / w‖ = ‖(t : ℂ)‖ / ‖w‖ := by
      exact norm_div _ _
    _ = ‖t‖ / ‖w‖ := by
      rw [Complex.normSq, Real.norm_eq_abs]

/-- On the lower split interval `0 < t ≤ ‖w‖ / 2`, the Binet arctangent
argument lies in the half disk. -/
theorem Complex.binetSecondFormula_small_interval_argument_norm_le_half
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have ht_norm : ‖t‖ = t :=
    Real.norm_of_nonneg (le_of_lt ht.1)
  have harg_norm :
      ‖(t : ℂ) / w‖ = t / ‖w‖ := by
    calc
      ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ :=
        Complex.norm_real_div_eq_real_norm_div t w
      _ = t / ‖w‖ := by
        rw [ht_norm]
  have hdiv_le : t / ‖w‖ ≤ (1 / 2 : ℝ) := by
    exact (div_le_iff₀ hw_norm_pos).mpr ht.2
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 / 2 : ℝ))
      harg_norm.symm
      hdiv_le

/-- Small-argument arctangent bound for the Binet kernel. -/
theorem Complex.binetSecondFormula_arctan_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∀ t : ℝ,
      0 < t →
        ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) →
        ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * (t / ‖w‖) := by
  intro t ht hsmall
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * ‖(t : ℂ) / w‖ :=
    Complex.norm_arctan_le_two_norm_of_norm_le_half hsmall
  have ht_norm : ‖t‖ = t :=
    Real.norm_of_nonneg (le_of_lt ht)
  have harg_norm :
      ‖(t : ℂ) / w‖ = t / ‖w‖ := by
    calc
      ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ :=
        Complex.norm_real_div_eq_real_norm_div t w
      _ = t / ‖w‖ := by
        rw [ht_norm]
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * x)
      harg_norm
      harctan

/-- Local division of the arctangent estimate by the positive Binet
denominator. -/
theorem Complex.binetSecondFormula_kernel_norm_le_of_small_argument
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : 0 < t)
    (hsmall : ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 * (t / ‖w‖)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ 2 * (t / ‖w‖) :=
    Complex.binetSecondFormula_arctan_norm_le hw_re_pos t ht hsmall
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht)
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ = ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      rw [hden_norm]
    _ ≤ (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg

/-- Local small-interval pointwise kernel estimate for the lower split piece. -/
theorem Complex.binetSecondFormula_kernel_norm_le_on_small_interval
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 * (t / ‖w‖)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      hw_re_pos ht.1
      (Complex.binetSecondFormula_small_interval_argument_norm_le_half
        hw_re_pos ht)

/-- Division of the arctangent estimate by the positive Binet denominator. -/
theorem Complex.binetSecondFormula_kernel_norm_le_of_arctan_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_small_argument
      hw_re_pos ht (hsmall t ht)

/-- Small-argument pointwise kernel estimate for Binet's second-formula
remainder. -/
theorem Complex.binetSecondFormula_kernel_norm_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Complex.binetSecondFormula_kernel_norm_le_of_arctan_norm_le hw_re_pos hsmall

/-- Small-argument sector form of the Binet-kernel estimate on the open right
half-plane. -/
theorem Complex.binetSecondFormula_kernel_norm_le_openRightHalfPlaneSector
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_re_pos : 0 < w.re)
    (hsmall : ∀ t : ℝ, 0 < t → ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ)) :
    ∀ t : ℝ,
      0 < t →
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
          (2 * (t / ‖w‖)) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact Complex.binetSecondFormula_kernel_norm_le hw_re_pos hsmall

end

end LFunctions
end Boundary
