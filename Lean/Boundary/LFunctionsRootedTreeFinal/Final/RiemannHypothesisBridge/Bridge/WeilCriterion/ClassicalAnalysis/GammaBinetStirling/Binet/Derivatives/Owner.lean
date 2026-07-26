import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Denominator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SlitPlaneDefinitions
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Binet formula: derivatives and kernel bounds

This file owns arctangent derivative computation, kernel differentiation,
and final kernel bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

/-- The rational factor appearing in the Binet arctangent argument has the
expected derivative on the open right half-plane. -/
theorem Complex.binet_arctan_argument_derivative
    {t : ℝ} {w : ℂ}
    (_ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => (t : ℂ) / z)
      (-(t : ℂ) / w ^ 2) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hraw :
      HasDerivAt
        (fun z : ℂ => (t : ℂ) * z⁻¹)
        ((t : ℂ) * (-(w ^ 2)⁻¹)) w :=
    (hasDerivAt_inv hw_ne).const_mul (t : ℂ)
  have hfun :
      (fun z : ℂ => (t : ℂ) * z⁻¹) =
        (fun z : ℂ => (t : ℂ) / z) := by
    funext z
    exact (div_eq_mul_inv (t : ℂ) z).symm
  have hderiv :
      (t : ℂ) * (-(w ^ 2)⁻¹) =
        -(t : ℂ) / w ^ 2 := by
    calc
      (t : ℂ) * (-(w ^ 2)⁻¹) =
          -((t : ℂ) * (w ^ 2)⁻¹) := by
        exact mul_neg (t : ℂ) ((w ^ 2)⁻¹)
      _ = -((t : ℂ) / w ^ 2) := by
        exact congrArg Neg.neg (Eq.symm (div_eq_mul_inv (t : ℂ) (w ^ 2)))
      _ = -(t : ℂ) / w ^ 2 := by
        exact neg_div' (w ^ 2) (t : ℂ)
  exact
    Eq.subst
      (motive := fun f : ℂ → ℂ =>
        HasDerivAt f (-(t : ℂ) / w ^ 2) w)
      hfun
      (Eq.subst
        (motive := fun d : ℂ =>
          HasDerivAt (fun z : ℂ => (t : ℂ) * z⁻¹) d w)
        hderiv
        hraw)

/-- The arctangent derivative needed for the Binet kernel after composing
`Complex.arctan` with `z ↦ (t : ℂ) / z` on the open right half-plane. -/
theorem Complex.arctan_t_div_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
      (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) w := by
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have harg_ne_I : (t : ℂ) / w ≠ Complex.I :=
    Complex.binet_arctan_argument_ne_I hw_re_pos
  have harg_ne_negI : (t : ℂ) / w ≠ -Complex.I :=
    Complex.binet_arctan_argument_ne_negI hw_re_pos
  have harg_slit :
      (1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane :=
    Complex.binet_arctan_log_argument_mem_slitPlane ht hw_re_pos
  have h_inner :
      HasDerivAt
        (fun z : ℂ => (t : ℂ) / z)
        (-(t : ℂ) / w ^ 2) w := by
    exact Complex.binet_arctan_argument_derivative ht hw_re_pos
  have h_outer :
      HasDerivAt
        Complex.arctan
        ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) ((t : ℂ) / w) := by
    exact
      Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
        harg_ne_I harg_ne_negI harg_slit
  have hcomp :
      HasDerivAt
        (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
        (((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2)) w := by
    exact h_outer.comp w h_inner
  have hden_ne : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 :=
    Complex.binet_arctan_derivative_denominator_ne_zero hw_re_pos
  have halg :
      ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2) =
        -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2) := by
    exact Complex.arctan_t_div_derivative_algebra hw_ne
  exact halg ▸ hcomp

/-- Pointwise derivative of the arctangent kernel in Binet's second-formula
remainder.  This is the branch-sensitive local analytic statement for
`Complex.arctan`, specialized to the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_hasDerivAt
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.arctan ((t : ℂ) / z) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Complex.binetSecondFormulaDerivativeKernel t w) w := by
  exact
    (Complex.arctan_t_div_hasDerivAt ht hw_re_pos).div_const
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- A small ball around a point in the open right half-plane remains in the
open right half-plane. -/
theorem Complex.exists_ball_subset_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z - w‖ < ε → 0 < z.re := by
  exact
    Exists.intro (w.re / 2)
      (And.intro (half_pos hw_re_pos) (fun z hz => by
        have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
          exact RCLike.abs_re_le_norm (z - w)
        have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
          lt_of_le_of_lt hre_le_norm hz
        have hre_lower : -(w.re / 2) < z.re - w.re :=
          (abs_lt.mp hre_abs_lt).1
        have hw_half_pos : 0 < w.re / 2 :=
          half_pos hw_re_pos
        have hhalf_lt_z : w.re / 2 < z.re := by
          calc
            w.re / 2 = w.re + (-(w.re / 2)) :=
              Real.half_eq_self_add_neg_half w.re
            _ < w.re + (z.re - w.re) :=
              add_lt_add_left hre_lower w.re
            _ = z.re :=
              Real.add_sub_self_right w.re z.re
        exact hw_half_pos.trans hhalf_lt_z))

/-- A small ball around a point in the open right half-plane has the explicit
real-part margin `w.re / 2`. -/
theorem Complex.exists_ball_subset_re_ge_half
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ z : ℂ, ‖z - w‖ < ε → w.re / 2 ≤ z.re := by
  exact
    Exists.intro (w.re / 2)
      (And.intro (half_pos hw_re_pos) (fun z hz => by
        have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
          exact RCLike.abs_re_le_norm (z - w)
        have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
          lt_of_le_of_lt hre_le_norm hz
        have hre_lower : -(w.re / 2) < z.re - w.re :=
          (abs_lt.mp hre_abs_lt).1
        have hhalf_lt_z : w.re / 2 < z.re := by
          calc
            w.re / 2 = w.re + (-(w.re / 2)) :=
              Real.half_eq_self_add_neg_half w.re
            _ < w.re + (z.re - w.re) :=
              add_lt_add_left hre_lower w.re
            _ = z.re :=
              Real.add_sub_self_right w.re z.re
        exact le_of_lt hhalf_lt_z))

/-- The elementary division rearrangement used by the differentiated Binet
kernel majorant. -/
theorem Real.binet_derivativeKernel_div_sq_div_eq
    {δ d t : ℝ}
    (_hδ_sq_ne : δ ^ 2 ≠ 0) :
    (t / δ ^ 2) / d = (1 / δ ^ 2) * (t / d) := by
  exact Real.div_sq_div_assoc δ d t

/-- Norm of the rational factor in the differentiated Binet kernel. -/
theorem Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖-(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2)‖ ≤ t / δ ^ 2 := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  have hδ_nonneg : 0 ≤ δ :=
    le_of_lt hδ_pos
  have hδ_sq_pos : 0 < δ ^ 2 :=
    sq_pos_of_pos hδ_pos
  have hD_lower : δ ^ 2 ≤ ‖D‖ := by
    exact
      Complex.binet_arctan_derivative_denominator_norm_lower
        hδ_nonneg hδ_le_re
  have hD_pos : 0 < ‖D‖ :=
    lt_of_lt_of_le hδ_sq_pos hD_lower
  have ht_norm : ‖(t : ℂ)‖ = t := by
    calc
      ‖(t : ℂ)‖ = |(t : ℝ)| := by
        exact RCLike.norm_ofReal t
      _ = t := Real.norm_of_nonneg (le_of_lt ht)
  have hnorm :
      ‖-(t : ℂ) / D‖ = t / ‖D‖ := by
    calc
      ‖-(t : ℂ) / D‖ = ‖-(t : ℂ)‖ / ‖D‖ := by
        exact norm_div _ _
      _ = ‖(t : ℂ)‖ / ‖D‖ := by
        exact congrArg (fun x : ℝ => x / ‖D‖) (norm_neg (t : ℂ))
      _ = t / ‖D‖ := by
        exact congrArg (fun x : ℝ => x / ‖D‖) ht_norm
  have hdiv :
      t / ‖D‖ ≤ t / δ ^ 2 :=
    div_le_div_of_nonneg_left
      (le_of_lt ht) hδ_sq_pos hD_lower
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ t / δ ^ 2)
      hnorm.symm
      hdiv

/-- Pointwise domination of the differentiated Binet kernel by the real Binet
majorant, with a real-part margin. -/
theorem Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
    {z : ℂ}
    {δ t : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_le_re : δ ≤ z.re)
    (ht : 0 < t) :
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤
      (1 / δ ^ 2) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let D : ℂ := z ^ 2 + (t : ℂ) ^ 2
  let E : ℂ := Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hrational :
      ‖-(t : ℂ) / D‖ ≤ t / δ ^ 2 :=
    Complex.binetSecondFormulaDerivativeKernel_rational_norm_le
      hδ_pos hδ_le_re ht
  have hden_norm : ‖E‖ = d := by
    calc
      ‖E‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
        exact Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = d :=
        Real.binetSecondFormula_exp_denominator_norm_eq ht
  have hd_nonneg : 0 ≤ d :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht)
  have hkernel_norm :
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := by
    calc
      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
          ‖(-(t : ℂ) / D) / E‖ := by
        rfl
      _ = ‖-(t : ℂ) / D‖ / ‖E‖ := by
        exact norm_div _ _
      _ = ‖-(t : ℂ) / D‖ / d := by
        exact congrArg (fun x : ℝ => ‖-(t : ℂ) / D‖ / x) hden_norm
  have hdiv :
      ‖-(t : ℂ) / D‖ / d ≤ (t / δ ^ 2) / d :=
    div_le_div_of_nonneg_right hrational hd_nonneg
  have hδ_sq_ne : δ ^ 2 ≠ 0 :=
    ne_of_gt (sq_pos_of_pos hδ_pos)
  have hrearrange :
      (t / δ ^ 2) / d =
        (1 / δ ^ 2) * (t / d) :=
    Real.binet_derivativeKernel_div_sq_div_eq hδ_sq_ne
  calc
    ‖Complex.binetSecondFormulaDerivativeKernel t z‖ =
        ‖-(t : ℂ) / D‖ / d := hkernel_norm
    _ ≤ (t / δ ^ 2) / d := hdiv
    _ = (1 / δ ^ 2) * (t / d) := hrearrange

/-- Local differentiability of the Binet arctangent kernel throughout a ball
inside the open right half-plane, in the form required by mathlib's
parameter-integral differentiation theorem. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∀ z : ℂ,
        ‖z - w‖ < ε →
          ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  match Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
  | Exists.intro ε hε_data =>
    exact
      Exists.intro ε
        (And.intro hε_data.1 (fun z hz =>
          Filter.mem_of_superset
            (MeasureTheory.self_mem_ae_restrict
              (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))
            (fun t ht =>
              Complex.binetSecondFormula_arctanKernel_hasDerivAt
                ht (hε_data.2 z hz))))

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  match Complex.exists_ball_subset_re_ge_half hw_re_pos with
  | Exists.intro ε hε_data =>
    let δ : ℝ := w.re / 2
    let g : ℝ → ℝ :=
      fun t : ℝ =>
        (1 / δ ^ 2) *
          (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    have hδ_pos : 0 < δ :=
      half_pos hw_re_pos
    have hg_integrable : IntegrableOn g (Set.Ioi (0 : ℝ)) := by
      exact
        Real.binetSecondFormula_kernel_majorant_integrableOn.const_mul
          (1 / δ ^ 2)
    exact
      Exists.intro ε
        (And.intro hε_data.1
          (Exists.intro g
            (And.intro hg_integrable (fun z hz t ht => by
              have hδ_le_re : δ ≤ z.re :=
                hε_data.2 z hz
              exact
                Complex.binetSecondFormulaDerivativeKernel_norm_le_scaled_majorant
                  hδ_pos hδ_le_re ht))))

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, stated pointwise before passing to the restricted
almost-everywhere filter. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ t : ℝ,
              t ∈ Set.Ioi (0 : ℝ) →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  exact
    Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
      hw_re_pos

/-- Local integrable domination for the differentiated arctangent kernel on
the positive `t`-axis, sufficient for differentiating the Binet remainder under
the integral sign near `w` in the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_locally_dominated
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  match
    Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
      hw_re_pos
  with
  | Exists.intro ε hε_data =>
    match hε_data.2 with
    | Exists.intro g hg_data =>
      exact
        Exists.intro ε
          (And.intro hε_data.1
            (Exists.intro g
              (And.intro hg_data.1 (fun z hz =>
                Filter.mem_of_superset
                  (MeasureTheory.self_mem_ae_restrict
                    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))
                  (fun t ht => hg_data.2 z hz t ht)))))

/-- Membership in a smaller ball gives the norm inequality needed for a larger
radius measured in the normed-space coordinates. -/
theorem Complex.norm_sub_lt_of_mem_ball_of_le_radius
    {w z : ℂ}
    {ε η : ℝ}
    (hε_le_η : ε ≤ η)
    (hz : z ∈ Metric.ball w ε) :
    ‖z - w‖ < η := by
  have hdist : dist z w < ε :=
    Metric.mem_ball.mp hz
  have hnorm : ‖z - w‖ < ε := by
    have hdist_eq : dist z w = ‖z - w‖ :=
      dist_eq_norm z w
    exact
      Eq.subst
        (motive := fun x : ℝ => x < ε)
        hdist_eq
        hdist
  exact lt_of_lt_of_le hnorm hε_le_η

/-- The a.e. arctangent-kernel derivative statement on a ball restricts to
any smaller ball. -/
theorem Complex.binetSecondFormula_arctanKernel_derivative_on_smaller_ball
    {w : ℂ}
    {ε η : ℝ}
    (hε_le_η : ε ≤ η)
    (hkernel :
      ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w η →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z) :
    ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
      ∀ z : ℂ,
        z ∈ Metric.ball w ε →
          HasDerivAt
            (fun u : ℂ =>
              Complex.arctan ((t : ℂ) / u) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
            (Complex.binetSecondFormulaDerivativeKernel t z) z :=
  hkernel.mono
    (fun t ht z hz =>
      ht z
        (Metric.mem_ball.mpr
          (by
            have hnorm : ‖z - w‖ < η :=
              Complex.norm_sub_lt_of_mem_ball_of_le_radius
                hε_le_η hz
            have hdist_eq : dist z w = ‖z - w‖ :=
              dist_eq_norm z w
            exact
              Eq.subst
                (motive := fun x : ℝ => x < η)
                hdist_eq.symm
                hnorm)))

/-- The a.e. derivative-kernel majorant on a ball restricts to any smaller
ball. -/
theorem Complex.binetSecondFormula_derivativeKernel_bound_on_smaller_ball
    {w : ℂ}
    {ε η : ℝ}
    {g : ℝ → ℝ}
    (hε_le_η : ε ≤ η)
    (hbound :
      ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w η →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
      ∀ z : ℂ,
        z ∈ Metric.ball w ε →
          ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t :=
  hbound.mono
    (fun t ht z hz =>
      ht z
        (Metric.mem_ball.mpr
          (by
            have hnorm : ‖z - w‖ < η :=
              Complex.norm_sub_lt_of_mem_ball_of_le_radius
                hε_le_η hz
            have hdist_eq : dist z w = ‖z - w‖ :=
              dist_eq_norm z w
            exact
              Eq.subst
                (motive := fun x : ℝ => x < η)
                hdist_eq.symm
                hnorm)))

/-- The Binet arctangent kernel is a.e.-strongly measurable on the positive
half-line. -/
theorem Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable
    (z : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / z) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / z) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
    have harg : Measurable (fun t : ℝ => (t : ℂ) / z) :=
      (Complex.measurable_ofReal.comp measurable_id).div_const z
    have hlog_arg :
        Measurable
          (fun t : ℝ =>
            Complex.log
              ((1 + ((t : ℂ) / z) * Complex.I) /
                (1 - ((t : ℂ) / z) * Complex.I))) :=
      Complex.measurable_log.comp
        (((measurable_const.add (harg.mul_const Complex.I))).div
          (measurable_const.sub (harg.mul_const Complex.I)))
    have harctan :
        Measurable
          (fun t : ℝ => Complex.arctan ((t : ℂ) / z)) := by
      show
        Measurable
          (fun t : ℝ =>
            (-Complex.I / 2) *
              Complex.log
                ((1 + ((t : ℂ) / z) * Complex.I) /
                  (1 - ((t : ℂ) / z) * Complex.I)))
      exact measurable_const.mul hlog_arg
    have hden :
        Measurable
          (fun t : ℝ =>
            Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
      have hlinear :
          Measurable (fun t : ℝ => (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp
          ((measurable_const.mul measurable_id))
      exact hlinear.cexp.sub measurable_const
    exact harctan.div hden
  exact hmeas.aestronglyMeasurable

/-- The differentiated Binet kernel is a.e.-strongly measurable on the positive
half-line. -/
theorem Complex.binetSecondFormulaDerivativeKernel_aestronglyMeasurable
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
      (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w) := by
    have ht_complex : Measurable (fun t : ℝ => (t : ℂ)) :=
      Complex.measurable_ofReal.comp measurable_id
    have hnum : Measurable (fun t : ℝ => -(t : ℂ)) :=
      ht_complex.neg
    have hden :
        Measurable (fun t : ℝ => w ^ 2 + (t : ℂ) ^ 2) :=
      measurable_const.add (ht_complex.pow_const 2)
    have hrational :
        Measurable (fun t : ℝ => -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) :=
      hnum.div hden
    have hexp_den :
        Measurable
          (fun t : ℝ =>
            Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
      have hlinear :
          Measurable (fun t : ℝ => (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)) :=
        Complex.measurable_ofReal.comp
          (measurable_const.mul measurable_id)
      exact hlinear.cexp.sub measurable_const
    show
      Measurable
        (fun t : ℝ =>
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
    exact hrational.div hexp_den
  exact hmeas.aestronglyMeasurable

/-- Early local small-argument estimate for the Binet arctangent argument. -/
theorem Complex.binetSecondFormula_small_interval_argument_norm_le_half_for_integrability
    {w : ℂ}
    {t : ℝ}
    (hw_re_pos : 0 < w.re)
    (ht : t ∈ Set.Ioc (0 : ℝ) (‖w‖ / 2)) :
    ‖(t : ℂ) / w‖ ≤ (1 / 2 : ℝ) := by
  exact
    Complex.binetSecondFormula_small_interval_argument_norm_le_half
      hw_re_pos ht

/-- Early small-interval pointwise domination for the Binet kernel. -/
theorem Complex.binetSecondFormula_kernel_norm_le_on_small_interval_for_integrability
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

/-- The Binet kernel is integrable on the lower split interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval
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
    (hM_integrable_Ioi.mono_set Set.Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    exact
      (Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable w).mono_measure
        (Measure.restrict_mono Set.Ioc_subset_Ioi_self le_rfl)
  have hpointwise :
      ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_kernel_norm_le_on_small_interval_for_integrability
          hw_re_pos ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Tail pointwise domination for the Binet kernel on the open right
half-plane after the split at `‖w‖ / 2`. -/
theorem Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant
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
  match
    Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound
      hw_re_pos
  with
  | Exists.intro C hC_data =>
    exact
      Exists.intro C
        (And.intro hC_data.1 (fun t ht_tail => by
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
            hC_data.2 t ht_tail
          calc
            ‖Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
                ‖Complex.arctan ((t : ℂ) / w)‖ /
                  ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
              exact norm_div _ _
            _ =
                ‖Complex.arctan ((t : ℂ) / w)‖ /
                  (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
              exact congrArg
                (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x)
                hden_norm
            _ ≤ (C * t) /
                  (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
              div_le_div_of_nonneg_right harctan hden_nonneg
            _ =
                C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
              exact
                mul_div_assoc C t
                  (Real.exp ((2 : ℝ) * Real.pi * t) - 1)))

/-- The Binet kernel is integrable on the upper split interval. -/
theorem Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
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
  match
    Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant
      hw_re_pos
  with
  | Exists.intro c hc_data =>
    have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
      Real.binetSecondFormula_kernel_majorant_integrableOn
    have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
      div_nonneg (norm_nonneg w) zero_le_two
    have hcM_integrable :
        Integrable (fun t : ℝ => c * M t)
          (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
      (hM_integrable_Ioi.mono_set (Set.Ioi_subset_Ioi hcut_nonneg)).const_mul c
    have hK_meas :
        AEStronglyMeasurable K
          (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
      exact
        (Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable w).mono_measure
          (Measure.restrict_mono (Set.Ioi_subset_Ioi hcut_nonneg) le_rfl)
    have hpointwise :
        ∀ᵐ (t : ℝ) ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
          ‖K t‖ ≤ c * M t :=
      (ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => hc_data.2 t ht)
    exact
      hcM_integrable.mono' hK_meas hpointwise

/-- The Binet arctangent kernel is integrable at each point of the open right
half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_integrable
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
    Complex.binetSecondFormula_arctanKernel_integrableOn_small_interval
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  have hK_integrable : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    hunion ▸ hsmall.union htail
  exact hK_integrable

/-- The arctangent kernel and differentiated Binet kernel have the measurability
and base-point integrability needed for dominated differentiation. -/
theorem Complex.binetSecondFormulaRemainder_integral_data
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (∀ᶠ z in 𝓝 w,
      AEStronglyMeasurable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / z) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))) := by
  exact
    ⟨Filter.Eventually.of_forall
        (fun z =>
          Complex.binetSecondFormula_arctanKernel_aestronglyMeasurable z),
      Complex.binetSecondFormula_arctanKernel_integrable hw_re_pos,
      Complex.binetSecondFormulaDerivativeKernel_aestronglyMeasurable w⟩

/-- Uniform-a.e. differentiability of the Binet arctangent kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
        ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
          ∀ z : ℂ,
            z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  match Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
  | Exists.intro ε hε_data =>
    exact
      Exists.intro ε
        (And.intro hε_data.1
          (Filter.mem_of_superset
            (MeasureTheory.self_mem_ae_restrict
              (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))
            (fun t ht z hz => by
              have hnorm : ‖z - w‖ < ε :=
                Complex.norm_sub_lt_of_mem_ball_of_le_radius
                  (le_refl ε) hz
              exact
                Complex.binetSecondFormula_arctanKernel_hasDerivAt
                  ht (hε_data.2 z hnorm))))

/-- Uniform-a.e. domination of the differentiated Binet kernel on one ball
inside the open right half-plane. -/
theorem Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ,
      0 < ε ∧
      ∃ g : ℝ → ℝ,
        IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
          ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  match
    Complex.binetSecondFormula_derivativeKernel_pointwise_bound_on_ball
      hw_re_pos
  with
  | Exists.intro ε hε_data =>
    match hε_data.2 with
    | Exists.intro g hg_data =>
      exact
        Exists.intro ε
          (And.intro hε_data.1
            (Exists.intro g
              (And.intro hg_data.1
                (Filter.mem_of_superset
                  (MeasureTheory.self_mem_ae_restrict
                    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))))
                  (fun t ht z hz => by
                    have hnorm : ‖z - w‖ < ε :=
                      Complex.norm_sub_lt_of_mem_ball_of_le_radius
                        (le_refl ε) hz
                    exact hg_data.2 z hnorm t ht)))))

/-- Dominated-differentiation transport for the Binet remainder once the
measurability and base-point integrability data have been supplied. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
    {w : ℂ}
    {ε : ℝ}
    (hε_pos : 0 < ε)
    (hF_meas :
      ∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF_int :
      Integrable
        (fun t : ℝ =>
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
        (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    {g : ℝ → ℝ}
    (hg_int :
      Integrable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hbound :
      ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t)
    (hdiff :
      ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
        ∀ z : ℂ,
          z ∈ Metric.ball w ε →
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  let μ : Measure ℝ := Measure.restrict volume (Set.Ioi (0 : ℝ))
  let F : ℂ → ℝ → ℂ :=
    fun z t =>
      Complex.arctan ((t : ℂ) / z) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let F' : ℂ → ℝ → ℂ :=
    fun z t => Complex.binetSecondFormulaDerivativeKernel t z
  have hmain :
      Integrable (F' w) μ ∧
        HasDerivAt
          (fun z : ℂ => ∫ t, F z t ∂μ)
          (∫ t, F' w t ∂μ) w := by
    exact
      hasDerivAt_integral_of_dominated_loc_of_deriv_le
        (μ := μ)
        (x₀ := w)
        (F := F)
        (F' := F')
        (bound := g)
        hε_pos
        (by exact hF_meas)
        (by exact hF_int)
        (by exact hF'_meas)
        (by exact hbound)
        (by exact hg_int)
        (by exact hdiff)
  have hscaled :
      HasDerivAt
        (fun z : ℂ => 2 * ∫ t, F z t ∂μ)
        (2 * ∫ t, F' w t ∂μ) w :=
    hmain.2.const_mul 2
  exact hscaled

/-- Integral derivative transport for the Binet second-formula remainder from
the pointwise arctangent-kernel derivative and its local integrable majorant. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
    {w : ℂ}
    (hdata :
      (∀ᶠ z in 𝓝 w,
        AEStronglyMeasurable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / z) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ)))) ∧
        Integrable
          (fun t : ℝ =>
            Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
          (Measure.restrict volume (Set.Ioi (0 : ℝ))) ∧
        AEStronglyMeasurable
          (fun t : ℝ => Complex.binetSecondFormulaDerivativeKernel t w)
          (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hkernel :
      ∃ ε : ℝ,
        0 < ε ∧
          ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            ∀ z : ℂ,
              z ∈ Metric.ball w ε →
              HasDerivAt
                (fun u : ℂ =>
                  Complex.arctan ((t : ℂ) / u) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                (Complex.binetSecondFormulaDerivativeKernel t z) z)
    (hdominated :
      ∃ ε : ℝ,
        0 < ε ∧
        ∃ g : ℝ → ℝ,
          IntegrableOn g (Set.Ioi (0 : ℝ)) ∧
            ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ∀ z : ℂ,
                z ∈ Metric.ball w ε →
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  match hdata with
  | And.intro hF_meas hdata_tail =>
    match hdata_tail with
    | And.intro hF_int hF'_meas =>
      match hkernel with
      | Exists.intro ε₁ hkernel_data =>
        match hdominated with
        | Exists.intro ε₂ hdominated_data =>
          match hdominated_data.2 with
          | Exists.intro g hg_data =>
            let ε : ℝ := min ε₁ ε₂
            have hε_pos : 0 < ε :=
              lt_min hkernel_data.1 hdominated_data.1
            have hε_le_ε₁ : ε ≤ ε₁ :=
              min_le_left ε₁ ε₂
            have hε_le_ε₂ : ε ≤ ε₂ :=
              min_le_right ε₁ ε₂
            have hdiff :
                ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
                  ∀ z : ℂ,
                    z ∈ Metric.ball w ε →
                      HasDerivAt
                        (fun u : ℂ =>
                          Complex.arctan ((t : ℂ) / u) /
                            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
                        (Complex.binetSecondFormulaDerivativeKernel t z) z :=
              Complex.binetSecondFormula_arctanKernel_derivative_on_smaller_ball
                hε_le_ε₁ hkernel_data.2
            have hbound :
                ∀ᵐ (t : ℝ) ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
                  ∀ z : ℂ,
                    z ∈ Metric.ball w ε →
                      ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t :=
              Complex.binetSecondFormula_derivativeKernel_bound_on_smaller_ball
                hε_le_ε₂ hg_data.2
            exact
              Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative_and_integrability
                hε_pos hF_meas hF_int hF'_meas hg_data.1 hbound hdiff

/-- Differentiation under the integral sign for the Binet second-formula
remainder. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
      (Complex.binetSecondFormulaRemainder_integral_data
        hw_re_pos)
      (Complex.binetSecondFormula_arctanKernel_local_hasDerivAt_uniform_ae
        hw_re_pos)
      (Complex.binetSecondFormula_derivativeKernel_locally_dominated_uniform_ae
        hw_re_pos)

/-- The logarithmic derivative of the principal-log Gamma side on the open
right half-plane, stated as the exact special-function derivative owner fact
needed for Binet's differentiated formula. -/
theorem Complex.logGamma_hasDerivAt_openRightHalfPlane_from_Gamma_derivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane) :
    HasDerivAt
      (fun z : ℂ => Complex.log (Complex.Gamma z))
      (deriv Complex.Gamma w / Complex.Gamma w) w := by
  have hnot_pole : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hw_eq
    have hre_nonpos : w.re ≤ 0 := by
      have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hw_eq
      have hneg_re : (-(n : ℂ)).re = -(n : ℝ) := by
        exact
          Eq.trans
            (Complex.neg_re (n : ℂ))
            (congrArg Neg.neg (Complex.natCast_re n))
      have hneg_nonpos : (-(n : ℂ)).re ≤ 0 :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ 0)
          hneg_re.symm
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ 0)
          hre.symm
          hneg_nonpos
    exact not_lt_of_ge hre_nonpos hw_re_pos
  have hgamma_deriv :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hnot_pole).hasDerivAt
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero hnot_pole
  exact hgamma_deriv.clog hgamma_slit

/-- Points in the open right half-plane lie in the principal-log slit plane. -/
theorem Complex.mem_slitPlane_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ∈ Complex.slitPlane := by
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hw_re_pos)

/-- Explicit derivative of the Binet logarithmic main term on the open right
half-plane. -/
theorem Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetLogGammaMainTerm
      (Complex.log w - (1 / (2 * w))) w := by
  have hw_ne_zero : w ≠ 0 :=
    Complex.ne_zero_of_re_pos hw_re_pos
  have hlog :
      HasDerivAt (fun z : ℂ => Complex.log z) (1 / w) w :=
    (hasDerivAt_id' w).clog
      (Complex.mem_slitPlane_of_re_pos hw_re_pos)
  have hfactor :
      HasDerivAt (fun z : ℂ => z - (1 / 2 : ℂ)) 1 w :=
    (hasDerivAt_id' w).sub_const (1 / 2 : ℂ)
  have hprod :
      HasDerivAt
        (fun z : ℂ => (z - (1 / 2 : ℂ)) * Complex.log z)
        (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) w :=
    hfactor.mul hlog
  have hmain :
      HasDerivAt
        (fun z : ℂ =>
          (z - (1 / 2 : ℂ)) * Complex.log z - z +
            (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)
        ((1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1) w :=
    ((hprod.sub (hasDerivAt_id' w)).add_const
      ((((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2))
  have hderiv :
      (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 =
        Complex.log w - (1 / (2 * w)) := by
    calc
      (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 =
          (1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1 + 0 := by
        exact
          Eq.symm
            (add_zero
              ((1 * Complex.log w + (w - (1 / 2 : ℂ)) * (1 / w)) - 1))
      _ = Complex.log w - (1 / (2 * w)) :=
        Complex.binetLogGammaMainTerm_derivative_algebra
          (w := w)
          (L := Complex.log w)
          hw_ne_zero
  exact
    Eq.subst
      (motive := fun d : ℂ =>
        HasDerivAt Complex.binetLogGammaMainTerm d w)
      hderiv
      hmain

/-- The explicit Binet main term is complex-differentiable on the open right
half-plane. -/
theorem Complex.binetLogGammaMainTerm_differentiableAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    DifferentiableAt ℂ Complex.binetLogGammaMainTerm w :=
  (Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
    hw_re_pos).differentiableAt

/-- The derivative value of the Binet logarithmic main term on the open right
half-plane. -/
theorem Complex.deriv_binetLogGammaMainTerm_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    deriv Complex.binetLogGammaMainTerm w =
      Complex.log w - (1 / (2 * w)) := by
  exact
    (Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
      hw_re_pos).deriv

/-- Derivative of the analytic Binet logarithm branch on the open right
half-plane. -/
theorem Complex.binetLogGammaBranch_hasDerivAt_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      Complex.binetLogGammaBranch
      ((Complex.log w - (1 / (2 * w))) +
        Complex.binetSecondFormulaRemainderDerivative w)
      w := by
  have hmain :
      HasDerivAt
        Complex.binetLogGammaMainTerm
        (Complex.log w - (1 / (2 * w))) w :=
    Complex.binetLogGammaMainTerm_hasDerivAt_openRightHalfPlane
      hw_re_pos
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  exact hmain.add hremainder

/-- The standard Binet log-derivative identity with the differentiated
arctangent-kernel integral written out.  This is the remaining special-function
input after the local derivative transport and Binet main-term derivative have
both been proved from local calculus. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  let D : ℂ :=
    (Complex.log w - (1 / (2 * w))) +
      Complex.binetSecondFormulaRemainderDerivative w
  have hbranch_deriv :
      HasDerivAt Complex.binetLogGammaBranch D w := by
    show
      HasDerivAt Complex.binetLogGammaBranch
        ((Complex.log w - (1 / (2 * w))) +
          Complex.binetSecondFormulaRemainderDerivative w)
        w
    exact
      Complex.binetLogGammaBranch_hasDerivAt_openRightHalfPlane
        hw_re_pos
  have hexp_branch_deriv :
      HasDerivAt
        (fun z : ℂ => Complex.exp (Complex.binetLogGammaBranch z))
        (Complex.exp (Complex.binetLogGammaBranch w) * D) w :=
    hbranch_deriv.cexp
  have heq_eventually :
      (fun z : ℂ => Complex.exp (Complex.binetLogGammaBranch z)) =ᶠ[𝓝 w]
        Complex.Gamma := by
    match Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    | Exists.intro ε hε_data =>
      have hball :
          ∀ᶠ z : ℂ in 𝓝 w, ‖z - w‖ < ε :=
        (Metric.eventually_nhds_iff_ball.2
          (Exists.intro ε
            (And.intro hε_data.1 (fun z hz => hz))))
      exact (hball.and hfinite_nhds).mono
        (fun z hzhfinite =>
          Complex.Gamma_binetSecondFormula_branchExponential
            (hε_data.2 z hzhfinite.1)
            hzhfinite.2)
  have hgamma_from_branch :
      HasDerivAt Complex.Gamma
        (Complex.exp (Complex.binetLogGammaBranch w) * D) w :=
    hexp_branch_deriv.congr_of_eventuallyEq heq_eventually.symm
  have hnot_pole : ∀ n : ℕ, w ≠ -(n : ℂ) := by
    intro n hw_eq
    have hre_nonpos : w.re ≤ 0 := by
      have hre : w.re = (-(n : ℂ)).re := congrArg Complex.re hw_eq
      have hneg_re : (-(n : ℂ)).re = -(n : ℝ) := by
        exact
          Eq.trans
            (Complex.neg_re (n : ℂ))
            (congrArg Neg.neg (Complex.natCast_re n))
      have hneg_nonpos : (-(n : ℂ)).re ≤ 0 :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ 0)
          hneg_re.symm
          (neg_nonpos.mpr (Nat.cast_nonneg n))
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ 0)
          hre.symm
          hneg_nonpos
    exact not_lt_of_ge hre_nonpos hw_re_pos
  have hgamma_deriv :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma w) w :=
    (Complex.differentiableAt_Gamma w hnot_pole).hasDerivAt
  have hderiv_eq :
      Complex.exp (Complex.binetLogGammaBranch w) * D =
        deriv Complex.Gamma w :=
    hgamma_from_branch.unique hgamma_deriv
  have hbranch_exp :
      Complex.exp (Complex.binetLogGammaBranch w) =
        Complex.Gamma w :=
    Complex.Gamma_binetSecondFormula_branchExponential hw_re_pos
      hfinite_w
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero hnot_pole
  have hgamma_mul_D :
      Complex.Gamma w * D = deriv Complex.Gamma w := by
    calc
      Complex.Gamma w * D =
          Complex.exp (Complex.binetLogGammaBranch w) * D := by
        exact congrArg (fun u : ℂ => u * D) hbranch_exp.symm
      _ = deriv Complex.Gamma w := hderiv_eq
  have hD_eq :
      D =
        deriv Complex.Gamma w / Complex.Gamma w := by
    calc
      D = (Complex.Gamma w)⁻¹ * (Complex.Gamma w * D) := by
        exact (inv_mul_cancel_left₀ hgamma_ne D).symm
      _ = (Complex.Gamma w)⁻¹ * deriv Complex.Gamma w := by
        exact congrArg (fun u : ℂ => (Complex.Gamma w)⁻¹ * u)
          hgamma_mul_D
      _ = deriv Complex.Gamma w * (Complex.Gamma w)⁻¹ := by
        exact mul_comm (Complex.Gamma w)⁻¹ (deriv Complex.Gamma w)
      _ = deriv Complex.Gamma w / Complex.Gamma w := by
        exact (div_eq_mul_inv (deriv Complex.Gamma w) (Complex.Gamma w)).symm
  exact hD_eq.symm

/-- The standard Binet log-derivative identity with the differentiated
arctangent-kernel integral written out. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_owner
      hw_re_pos hfinite_w hfinite_nhds

/-- Canonical branch-correct name for the Abel--Plana logarithmic-derivative
owner.  This surface deliberately carries no principal-log slit hypothesis. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_branch_owner
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
              Complex.binetAbelPlanaFiniteContourRemainder N z) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
  Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral_owner
    hw_re_pos hfinite_w hfinite_nhds

/-- The standard Binet log-derivative identity in the local remainder-derivative
normalization used by this file. -/
theorem Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    deriv Complex.Gamma w / Complex.Gamma w =
      (Complex.log w - (1 / (2 * w))) +
        Complex.binetSecondFormulaRemainderDerivative w := by
  exact
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_integral
      hw_re_pos hfinite_w hfinite_nhds

/-- The differentiated Binet identity at the logarithmic-derivative level:
the Gamma logarithmic derivative minus the derivative of the explicit main
term is the derivative of the Binet remainder. -/
theorem Complex.Gamma_logDerivative_sub_binetMainTerm_derivative_eq_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    deriv Complex.Gamma w / Complex.Gamma w -
        deriv Complex.binetLogGammaMainTerm w =
      Complex.binetSecondFormulaRemainderDerivative w := by
  have hmain :
      deriv Complex.binetLogGammaMainTerm w =
        Complex.log w - (1 / (2 * w)) :=
    Complex.deriv_binetLogGammaMainTerm_openRightHalfPlane hw_re_pos
  have hlogderiv :
      deriv Complex.Gamma w / Complex.Gamma w =
        (Complex.log w - (1 / (2 * w))) +
          Complex.binetSecondFormulaRemainderDerivative w :=
    Complex.Gamma_logDerivative_eq_binet_explicit_derivative_add_remainderDerivative
      hw_re_pos hfinite_w hfinite_nhds
  calc
    deriv Complex.Gamma w / Complex.Gamma w -
        deriv Complex.binetLogGammaMainTerm w =
        ((Complex.log w - (1 / (2 * w))) +
          Complex.binetSecondFormulaRemainderDerivative w) -
            (Complex.log w - (1 / (2 * w))) := by
          have hA :
              deriv Complex.Gamma w / Complex.Gamma w =
                (Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w :=
            hlogderiv
          have hB :
              deriv Complex.binetLogGammaMainTerm w =
                Complex.log w - (1 / (2 * w)) :=
            hmain
          calc
            deriv Complex.Gamma w / Complex.Gamma w -
                deriv Complex.binetLogGammaMainTerm w =
                (((Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w) -
                    deriv Complex.binetLogGammaMainTerm w) := by
              exact congrArg
                (fun x : ℂ => x - deriv Complex.binetLogGammaMainTerm w) hA
            _ =
                ((Complex.log w - (1 / (2 * w))) +
                  Complex.binetSecondFormulaRemainderDerivative w) -
                    (Complex.log w - (1 / (2 * w))) := by
              exact congrArg
                (fun x : ℂ =>
                  ((Complex.log w - (1 / (2 * w))) +
                    Complex.binetSecondFormulaRemainderDerivative w) - x) hB
    _ = Complex.binetSecondFormulaRemainderDerivative w := by
          exact
            add_sub_cancel_left
              (Complex.log w - (1 / (2 * w)))
              (Complex.binetSecondFormulaRemainderDerivative w)

/-- The derivative of the principal-log Gamma side minus the explicit Binet
main term, reduced to the logarithmic-derivative Binet identity. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_from_logDerivative_identity
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  have hlog :
      HasDerivAt
        (fun z : ℂ => Complex.log (Complex.Gamma z))
        (deriv Complex.Gamma w / Complex.Gamma w) w :=
    Complex.logGamma_hasDerivAt_openRightHalfPlane_from_Gamma_derivative
      hw_re_pos hgamma_slit
  have hmain :
      HasDerivAt
        Complex.binetLogGammaMainTerm
        (deriv Complex.binetLogGammaMainTerm w) w :=
    (Complex.binetLogGammaMainTerm_differentiableAt_openRightHalfPlane
      hw_re_pos).hasDerivAt
  have hsub :=
    hlog.sub hmain
  have hderiv_eq :
      deriv Complex.Gamma w / Complex.Gamma w -
          deriv Complex.binetLogGammaMainTerm w =
        Complex.binetSecondFormulaRemainderDerivative w :=
    Complex.Gamma_logDerivative_sub_binetMainTerm_derivative_eq_remainderDerivative
      hw_re_pos hfinite_w hfinite_nhds
  exact hderiv_eq ▸ hsub

/-- The special-function derivative identity behind Binet's second
formula: the logarithmic derivative of Gamma minus the derivative of the
explicit Binet main term is the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_from_logDerivative_identity
      hw_re_pos hgamma_slit hfinite_w hfinite_nhds

/-- The logarithmic Gamma side and explicit Binet main term have the
derivative prescribed by the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
      hw_re_pos hgamma_slit hfinite_w hfinite_nhds

/-- The logarithmic Gamma side, after subtracting the explicit Binet main
term, has derivative equal to the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
      hw_re_pos hgamma_slit hfinite_w hfinite_nhds

/-- Differentiating the arctangent-kernel integral under the integral sign
gives the same logarithmic derivative as the Gamma side after subtracting the
explicit Binet main term. -/
theorem Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  have hlog_main :
      HasDerivAt
        (fun z : ℂ =>
          Complex.log (Complex.Gamma z) -
            Complex.binetLogGammaMainTerm z)
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
      hw_re_pos hgamma_slit hfinite_w hfinite_nhds
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  have hraw :
      HasDerivAt
        (fun z : ℂ =>
          (Complex.log (Complex.Gamma z) -
            Complex.binetLogGammaMainTerm z) -
              Complex.binetSecondFormulaRemainder z)
        (Complex.binetSecondFormulaRemainderDerivative w -
          Complex.binetSecondFormulaRemainderDerivative w) w :=
    hlog_main.sub hremainder
  have hfun :
      (fun z : ℂ =>
          (Complex.log (Complex.Gamma z) -
            Complex.binetLogGammaMainTerm z) -
              Complex.binetSecondFormulaRemainder z) =
        (fun z : ℂ =>
          Complex.log (Complex.Gamma z) -
            (Complex.binetLogGammaMainTerm z +
              Complex.binetSecondFormulaRemainder z)) := by
    funext z
    exact sub_sub (Complex.log (Complex.Gamma z))
      (Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainder z)
  have hderiv_zero :
      Complex.binetSecondFormulaRemainderDerivative w -
          Complex.binetSecondFormulaRemainderDerivative w =
        0 :=
    sub_self (Complex.binetSecondFormulaRemainderDerivative w)
  exact
    Eq.subst
      (motive := fun f : ℂ → ℂ => HasDerivAt f 0 w)
      hfun
      (Eq.subst
        (motive := fun d : ℂ =>
          HasDerivAt
            (fun z : ℂ =>
              (Complex.log (Complex.Gamma z) -
                Complex.binetLogGammaMainTerm z) -
                  Complex.binetSecondFormulaRemainder z)
            d w)
        hderiv_zero
        hraw)

/-- A complex function with zero derivative on the open right half-plane is
constant there.  This is the convex-domain mean-value theorem specialized to
the right half-plane. -/
theorem Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
    {F : ℂ → ℂ}
    (hderiv : ∀ {z : ℂ}, 0 < z.re → HasDerivAt F 0 z) :
    ∀ {z w : ℂ}, 0 < z.re → 0 < w.re → F z = F w := by
  intro z w hz hw
  let S : Set ℂ := {u : ℂ | 0 < u.re}
  have hconv : Convex ℝ S := by
    exact convex_halfSpace_re_gt (r := 0)
  have hopen : IsOpen S := by
    exact
      (isOpen_lt continuous_const Complex.continuous_re :
        IsOpen {u : ℂ | (0 : ℝ) < u.re})
  have hdiff : DifferentiableOn ℂ F S := by
    intro u hu
    exact (hderiv hu).differentiableAt.differentiableWithinAt
  have hzero :
      ∀ u ∈ S, fderivWithin ℂ F S u = 0 := by
    intro u hu
    have hunique : UniqueDiffWithinAt ℂ S u :=
      hopen.uniqueDiffWithinAt hu
    have hfderiv :
        fderivWithin ℂ F S u =
          ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0 : ℂ) :=
      (hderiv hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin hunique
    have hclm_zero :
        ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (0 : ℂ) =
          (0 : ℂ →L[ℂ] ℂ) := by
      exact ContinuousLinearMap.ext (fun v => smul_zero v)
    exact Eq.trans hfderiv hclm_zero
  exact hconv.is_const_of_fderivWithin_eq_zero hdiff hzero hz hw

/-- The two sides of Binet's second formula have the same complex derivative
on the open right half-plane.

This is the analytic continuation/differentiation root: after differentiating
the arctangent-kernel integral under the integral sign, the derivative agrees
with the logarithmic derivative of `Gamma` minus the derivative of the explicit
main term. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hgamma_slit : Complex.Gamma w ∈ Complex.slitPlane)
    (hfinite_w :
      ∀ N : ℕ,
        Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
          Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
              Complex.binetAbelPlanaFiniteContourRemainder N w)
    (hfinite_nhds :
      ∀ᶠ z : ℂ in 𝓝 w,
        ∀ N : ℕ,
          Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
            Complex.binetAbelPlanaFiniteMainTerm N z +
              Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                Complex.binetAbelPlanaFiniteContourRemainder N z) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  exact
    Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
      hw_re_pos hgamma_slit hfinite_w hfinite_nhds

/-- A holomorphic Binet difference with zero derivative on the open right
half-plane is determined there by its positive-real values. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
    (hreal :
      ∀ {x : ℝ},
        0 < x →
          Complex.log (Complex.Gamma (x : ℂ)) =
            Complex.binetLogGammaMainTerm (x : ℂ) +
              Complex.binetSecondFormulaRemainder (x : ℂ))
    (hderiv :
      ∀ {w : ℂ},
        0 < w.re →
          HasDerivAt
            (fun z : ℂ =>
              Complex.log (Complex.Gamma z) -
                (Complex.binetLogGammaMainTerm z +
                  Complex.binetSecondFormulaRemainder z))
            0 w) :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  intro w hw
  let F : ℂ → ℂ :=
    fun z : ℂ =>
      Complex.log (Complex.Gamma z) -
        (Complex.binetLogGammaMainTerm z +
          Complex.binetSecondFormulaRemainder z)
  have hbase_re : 0 < (w.re : ℂ).re := by
    exact hw
  have hconstant : F (w.re : ℂ) = F w :=
    Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
      (F := F)
      (fun hz => hderiv hz)
      hbase_re hw
  have hbase_zero : F (w.re : ℂ) = 0 := by
    show
      Complex.log (Complex.Gamma (w.re : ℂ)) -
          (Complex.binetLogGammaMainTerm (w.re : ℂ) +
            Complex.binetSecondFormulaRemainder (w.re : ℂ)) =
        0
    exact sub_eq_zero.mpr (hreal hw)
  have hw_zero : F w = 0 := by
    exact Eq.trans hconstant.symm hbase_zero
  exact sub_eq_zero.mp hw_zero

/- The branch input for the Binet identity is pointwise.  The older theorem
   above exposed it as a global half-plane hypothesis, although the derivative
   calculation only needs the value at the point being evaluated. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_local_slit
    (w : ℂ)
    (hw_re : 0 < w.re)
    (hgamma_w : Complex.Gamma w ∈ Complex.slitPlane)
    (hgamma_slit : Complex.GammaRightHalfPlaneSlitPlaneControl)
    (hfinite_real :
      ∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ))
    (hfinite_local :
      ∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) :
    Complex.log (Complex.Gamma w) =
      Complex.binetLogGammaMainTerm w +
        Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
      (fun hx =>
        Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
          hx (hfinite_real _ hx))
      (fun {w'} hw_pos =>
        Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
          (w := w') hw_pos (hgamma_slit w' hw_pos)
            (hfinite_local _ hw_pos).1 (hfinite_local _ hw_pos).2)
      w hw_re

/-- The open right half-plane is connected to the positive real axis by
paths along which the principal-log Binet difference has zero derivative.

This consumes the real-axis normalization and the zero-derivative identity to
propagate Binet's formula through the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative :
    ∀ w : ℂ,
      0 < w.re →
      (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
      (∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
      (∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) →
        Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  intro w hw hgamma_slit_open hfinite_real hfinite_open
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
      (fun hx =>
        Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
          hx (hfinite_real _ hx))
      (fun hw_re_pos =>
        Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
          hw_re_pos
          (hgamma_slit_open _ hw_re_pos)
          (hfinite_open _ hw_re_pos).1
          (hfinite_open _ hw_re_pos).2)
      w hw

/-- The classical second Binet integral representation, with the principal
logarithm normalization used by `Complex.binetLogGammaMainTerm` and the
literal arctangent-kernel remainder used in this package. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_principalLog :
    ∀ w : ℂ,
      0 < w.re →
      (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
      (∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
      (∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative

/-- Binet's logarithmic identity follows from the classical second Binet
integral representation on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation :
    ∀ w : ℂ,
      0 < w.re →
      (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
      (∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
      (∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_principalLog

/-- Binet's second logarithmic formula on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane :
    ∀ w : ℂ,
      0 < w.re →
      (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
      (∀ x : ℝ,
        0 < x →
          ∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
              Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                  Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
      (∀ z : ℂ,
        0 < z.re →
          (∀ N : ℕ,
            Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
              Complex.binetAbelPlanaFiniteMainTerm N z +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                  Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
          (∀ᶠ y : ℂ in 𝓝 z,
            ∀ N : ℕ,
              Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                Complex.binetAbelPlanaFiniteMainTerm N y +
                  Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                    Complex.binetAbelPlanaFiniteContourRemainder N y)) →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_from_integral_representation

/-- The literal arctangent-kernel Binet formula is an open-right-half-plane
statement.  On the boundary `w = i y`, the kernel crosses the principal
arctangent branch point at `t = y`, so this theorem records the large-radius
form for the existing pointwise integral only on `0 < w.re`. -/
theorem Complex.Gamma_binetSecondFormula_large_openRightHalfPlane :
      ∃ R : ℝ,
        0 < R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
          (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
          (∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
          (∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y)) →
          Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w := by
    exact
      Exists.intro 1
        (And.intro zero_lt_one (fun w hw_re_pos _hR hgamma_slit_open hfinite_real hfinite_open =>
          Complex.Gamma_binetSecondFormula_openRightHalfPlane
            w hw_re_pos hgamma_slit_open hfinite_real hfinite_open))

/- The large-radius form with the mathematically minimal branch input. -/
theorem Complex.Gamma_binetSecondFormula_large_openRightHalfPlane_of_local_slit :
      ∃ R : ℝ,
        0 < R ∧
        ∀ w : ℂ,
        0 < w.re →
          R ≤ ‖w‖ →
          Complex.Gamma w ∈ Complex.slitPlane →
          Complex.GammaRightHalfPlaneSlitPlaneControl →
          (∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
          (∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y)) →
          Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro w hw_re _hnorm hgamma hgamma_slit hreal hlocal
  exact Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_local_slit
    w hw_re hgamma hgamma_slit hreal hlocal

/-- Large-radius Binet formula for the existing principal-arctangent integral.
The hypothesis is open half-plane because the current remainder is the
pointwise kernel integral, not a boundary-value object on the imaginary axis. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation :
      ∃ R : ℝ,
        0 < R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
          (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
          (∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
          (∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y)) →
          Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_large_openRightHalfPlane

/-- Closed-sector continuation of Binet's second logarithmic formula after a
large-radius cutoff for the literal open-half-plane arctangent remainder. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation :
      ∃ R : ℝ,
        0 < R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
          (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
          (∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
          (∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y)) →
          Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation

/-- Binet's second logarithmic formula for Gamma in the open right half-plane,
away from the origin and after a fixed large-radius cutoff. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane :
      ∃ R : ℝ,
        0 < R ∧
        ∀ w : ℂ,
          0 < w.re →
          R ≤ ‖w‖ →
          (∀ z : ℂ, 0 < z.re → Complex.Gamma z ∈ Complex.slitPlane) →
          (∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ)) →
          (∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y)) →
          Complex.log (Complex.Gamma w) =
            Complex.binetLogGammaMainTerm w +
              Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation

end

end LFunctions
end Boundary
