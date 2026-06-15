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

/-- The scalar factor in the lower Binet kernel majorant can be reassociated. -/
theorem Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_reassociate
    (t : ℝ)
    (r : ℝ)
    (D : ℝ) :
    (2 * (t / r)) / D = (2 / r) * (t / D) := by
  calc
    (2 * (t / r)) / D = (2 * (t * r⁻¹)) * D⁻¹ := by
      exact congrArg (fun x : ℝ => (2 * x) * D⁻¹) (div_eq_mul_inv t r)
    _ = 2 * t * r⁻¹ * D⁻¹ := by
      exact congrArg (fun x : ℝ => x * D⁻¹) (mul_assoc 2 t r⁻¹)
    _ = 2 * r⁻¹ * (t * D⁻¹) := by
      calc
        2 * t * r⁻¹ * D⁻¹ = (2 * t) * r⁻¹ * D⁻¹ := rfl
        _ = 2 * t * (r⁻¹ * D⁻¹) := by
          exact mul_assoc (2 * t) r⁻¹ D⁻¹
        _ = 2 * (t * (r⁻¹ * D⁻¹)) := by
          exact (mul_assoc 2 t (r⁻¹ * D⁻¹)).symm
        _ = 2 * ((t * r⁻¹) * D⁻¹) := by
          exact congrArg (fun x : ℝ => 2 * x) (mul_assoc t r⁻¹ D⁻¹).symm
        _ = 2 * ((r⁻¹ * t) * D⁻¹) := by
          exact congrArg (fun x : ℝ => 2 * (x * D⁻¹)) (mul_comm t r⁻¹)
        _ = 2 * (r⁻¹ * (t * D⁻¹)) := by
          exact congrArg (fun x : ℝ => 2 * x) (mul_assoc r⁻¹ t D⁻¹)
        _ = 2 * r⁻¹ * (t * D⁻¹) := by
          exact mul_assoc 2 r⁻¹ (t * D⁻¹)
    _ = (2 / r) * (t / D) := by
      exact congrArg₂ (fun a b : ℝ => a * b)
        (div_eq_mul_inv 2 r).symm
        (div_eq_mul_inv t D).symm

/-- Rewriting the lower split kernel majorant into constant-times-majorant
form. -/
theorem Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_eq
    (t : ℝ)
    (r : ℝ) :
    (2 * (t / r)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
      (2 / r) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_reassociate
    t r (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- Norm of the Binet exponential denominator agrees with the positive real
denominator. -/
theorem Complex.binetSecondFormula_exp_denominator_norm_eq
    (t : ℝ) :
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
      ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
  calc
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        ‖((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ)‖ := by
      have hcoe :
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
            ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
        calc
          Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 =
              ((Real.exp ((2 : ℝ) * Real.pi * t) : ℝ) : ℂ) - 1 := by
            exact congrArg (fun z : ℂ => z - 1) (Complex.ofReal_exp _)
          _ = ((Real.exp ((2 : ℝ) * Real.pi * t) - 1 : ℝ) : ℂ) := by
            rfl
      exact congrArg norm hcoe
    _ = ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
      exact Complex.norm_ofReal _

/-- Norm of the Binet arctangent argument. -/
theorem Complex.norm_real_div_eq_real_norm_div
    (t : ℝ)
    (w : ℂ) :
    ‖(t : ℂ) / w‖ = ‖t‖ / ‖w‖ := by
  calc
    ‖(t : ℂ) / w‖ = ‖(t : ℂ)‖ / ‖w‖ := by
      exact norm_div _ _
    _ = ‖t‖ / ‖w‖ := by
      exact Complex.norm_ofReal _

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
    cases hw_zero
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
        exact congrArg (fun x : ℝ => x / ‖w‖) ht_norm
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
        exact congrArg (fun x : ℝ => x / ‖w‖) ht_norm
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
      exact congrArg (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x) hden_norm
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

/-- Owner-form lower split domination for the Binet arctangent kernel. -/
theorem Complex.binetSecondFormula_kernel_norm_le_on_small_interval_owner
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 / ‖w‖) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  have hkernel :
      ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Complex.binetSecondFormula_kernel_norm_le_on_small_interval
      hw_re_pos ht
  have hrewrite :
      (2 * (t / ‖w‖)) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
        (2 / ‖w‖) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :=
    Real.binetSecondFormula_two_mul_div_norm_div_exp_sub_one_eq
      t ‖w‖
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤ x)
      hrewrite
      hkernel

/-- Owner-form integrability of the Binet arctangent kernel on the lower split
interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioc (0 : ℝ) (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_kernel_norm_le_on_small_interval_owner
          hw_re_pos ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Owner-form tail domination for the Binet arctangent kernel. -/
theorem Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            C *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases
      Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound
        hw_re_pos with
    ⟨C, hC_nonneg, harctan_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_pos : 0 < t :=
    lt_of_le_of_lt
      (div_nonneg (norm_nonneg w) zero_le_two)
      ht_tail
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht_pos
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t :=
    harctan_bound t ht_tail
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      exact congrArg (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x) hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact (mul_div_assoc C t (Real.exp ((2 : ℝ) * Real.pi * t) - 1)).symm

/-- Owner-form integrability of the Binet arctangent kernel on the upper split
interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant_owner
        hw_re_pos with
    ⟨c, _hc_nonneg, htail_bound⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
    have hmeas : Measurable K := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Owner-form integrability of the Binet arctangent kernel on the positive
half-line. -/
theorem Complex.binetSecondFormula_arctanKernel_integrable_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Integrable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) zero_le_two
  have hsmall : IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval_owner
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval_owner
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  have hK_integrable : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    hunion ▸ hsmall.union htail
  exact hK_integrable

end

end LFunctions
end Boundary
