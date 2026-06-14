import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# Binet formula and kernel estimates

This file owns Binet's second logarithmic formula and the real majorant
estimates for its kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The derivative kernel obtained by differentiating
`arctan ((t : ℂ) / w)` in Binet's second-formula remainder. -/
noncomputable def Complex.binetSecondFormulaDerivativeKernel
    (t : ℝ) (w : ℂ) : ℂ :=
  (-(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2)) /
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The candidate derivative of the Binet second-formula remainder after
differentiating under the integral sign. -/
noncomputable def Complex.binetSecondFormulaRemainderDerivative
    (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetSecondFormulaDerivativeKernel t w

/-- The exact classical positive-real Binet identity in the normalization used
by this file.  This is the classical analytic input; mathlib currently exposes
Gamma integral and Bohr-Mollerup infrastructure but not this arctangent-kernel
Binet formula as a theorem. -/
theorem Complex.Gamma_binetSecondFormula_positiveReal_from_classical_Binet
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  sorry

/-- Classical Binet's second formula on the positive real axis, with the
principal logarithm and the arctangent-kernel remainder as normalized in this
file. -/
theorem Complex.Gamma_binetSecondFormula_positiveReal_classical_identity
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  exact
    Complex.Gamma_binetSecondFormula_positiveReal_from_classical_Binet hx

/-- Binet's second formula on the positive real axis with the principal-log
normalization used in this package.

This is the basepoint/real-axis normalization input for the complex
open-half-plane identity. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
    {x : ℝ}
    (hx : 0 < x) :
    Complex.log (Complex.Gamma (x : ℂ)) =
      Complex.binetLogGammaMainTerm (x : ℂ) +
        Complex.binetSecondFormulaRemainder (x : ℂ) := by
  exact
    Complex.Gamma_binetSecondFormula_positiveReal_classical_identity hx

/-- The principal complex arctangent has derivative `1 / (1 + z^2)` at points
where its defining logarithm is differentiable.  The extra `slitPlane`
hypothesis is essential for the principal branch of `Complex.log`. -/
theorem Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
    {z : ℂ}
    (hzI : z ≠ Complex.I)
    (hznegI : z ≠ -Complex.I)
    (hzslit :
      (1 + z * Complex.I) / (1 - z * Complex.I) ∈ Complex.slitPlane) :
    HasDerivAt
      Complex.arctan
      ((1 : ℂ) / (1 + z ^ 2)) z := by
  have hnum_ne : 1 + z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]
        _ = (-1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = -1 := by
            exact add_eq_zero_iff_eq_neg.mp hzero
          rw [hzI_eq]
        _ = Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hzI hz_eq
  have hden_ne : 1 - z * Complex.I ≠ 0 := by
    intro hzero
    have hz_eq : z = -Complex.I := by
      calc
        z = z * Complex.I / Complex.I := by
          rw [mul_div_cancel_right₀ _ Complex.I_ne_zero]
        _ = (1 : ℂ) / Complex.I := by
          have hzI_eq : z * Complex.I = 1 := by
            exact sub_eq_zero.mp hzero
          rw [hzI_eq]
        _ = -Complex.I := by
          field_simp [Complex.I_ne_zero, Complex.I_mul_I]
    exact hznegI hz_eq
  let q : ℂ → ℂ :=
    fun u : ℂ => (1 + u * Complex.I) / (1 - u * Complex.I)
  have hq :
      HasDerivAt q
        ((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) z := by
    have hnum :
        HasDerivAt (fun u : ℂ => 1 + u * Complex.I) Complex.I z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_add 1
    have hden :
        HasDerivAt (fun u : ℂ => 1 - u * Complex.I) (-Complex.I) z := by
      exact ((hasDerivAt_id' z).mul_const Complex.I).const_sub 1
    have hdiv := hnum.div hden hden_ne
    simpa [q] using hdiv
  have hlog :
      HasDerivAt
        (fun u : ℂ => Complex.log (q u))
        (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
          ((1 + z * Complex.I) / (1 - z * Complex.I))) z :=
    hq.clog hzslit
  have hscaled :
      HasDerivAt
        (fun u : ℂ => (-Complex.I / 2) * Complex.log (q u))
        ((-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I)))) z :=
    hlog.const_mul (-Complex.I / 2)
  have halg :
      (-Complex.I / 2) *
          (((2 : ℂ) * Complex.I / (1 - z * Complex.I) ^ 2) /
            ((1 + z * Complex.I) / (1 - z * Complex.I))) =
        (1 : ℂ) / (1 + z ^ 2) := by
    have hprod_ne : 1 + z ^ 2 ≠ 0 := by
      have hfactor :
          (1 - z * Complex.I) * (1 + z * Complex.I) = 1 + z ^ 2 := by
        ring_nf
      intro hzero
      exact (mul_ne_zero hden_ne hnum_ne) (hfactor.trans hzero)
    field_simp [hnum_ne, hden_ne, hprod_ne]
    ring_nf
  simpa [Complex.arctan, q, halg]
    using hscaled

/-- A point in the open right half-plane is nonzero. -/
theorem Complex.ne_zero_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ≠ 0 := by
  intro hw
  have hre_zero : w.re = 0 := by
    simpa [hw]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq hre_zero)

/-- Adding a purely imaginary number to a point in the open right half-plane
cannot give zero. -/
theorem Complex.add_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w + (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w + (t : ℂ) * Complex.I).re = 0 := by
    simpa [hzero]
  have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re := by
    simp [Complex.add_re, Complex.mul_re]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- Subtracting a purely imaginary number from a point in the open right
half-plane cannot give zero. -/
theorem Complex.sub_real_mul_I_ne_zero_of_re_pos
    {w : ℂ} {t : ℝ}
    (hw_re_pos : 0 < w.re) :
    w - (t : ℂ) * Complex.I ≠ 0 := by
  intro hzero
  have hre_zero : (w - (t : ℂ) * Complex.I).re = 0 := by
    simpa [hzero]
  have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re := by
    simp [Complex.sub_re, Complex.mul_re]
  exact (lt_irrefl (0 : ℝ)) (hw_re_pos.trans_eq (hre_eq.symm.trans hre_zero))

/-- The algebraic denominator `w^2 + t^2` in the differentiated Binet kernel
does not vanish in the open right half-plane. -/
theorem Complex.binet_arctan_derivative_denominator_ne_zero
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  have hplus :
      w + (t : ℂ) * Complex.I ≠ 0 :=
    Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hminus :
      w - (t : ℂ) * Complex.I ≠ 0 :=
    Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos
  have hfactor :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) =
        w ^ 2 + (t : ℂ) ^ 2 := by
    calc
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I)
          = w ^ 2 - ((t : ℂ) * Complex.I) ^ 2 := by
            ring
      _ = w ^ 2 + (t : ℂ) ^ 2 := by
            simp [Complex.I_mul_I]
  intro hzero
  have hprod_zero :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) = 0 :=
    hfactor.trans hzero
  exact
    (mul_ne_zero hplus hminus) hprod_zero

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_I
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w + (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          rw [div_mul_cancel₀ _ hw_ne]
        _ = Complex.I * w := by
          rw [h]
    calc
      w + (t : ℂ) * Complex.I
          = w + (Complex.I * w) * Complex.I := by
            rw [hmul]
      _ = 0 := by
            ring_nf
  exact (Complex.add_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- For `t > 0`, the Binet arctangent argument avoids the branch point `-I`
in the open right half-plane. -/
theorem Complex.binet_arctan_argument_ne_negI
    {t : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    (t : ℂ) / w ≠ -Complex.I := by
  intro h
  have hw_ne : w ≠ 0 := Complex.ne_zero_of_re_pos hw_re_pos
  have hzero : w - (t : ℂ) * Complex.I = 0 := by
    have hmul : (t : ℂ) = -Complex.I * w := by
      calc
        (t : ℂ) = ((t : ℂ) / w) * w := by
          rw [div_mul_cancel₀ _ hw_ne]
        _ = -Complex.I * w := by
          rw [h]
    calc
      w - (t : ℂ) * Complex.I
          = w - (-Complex.I * w) * Complex.I := by
            rw [hmul]
      _ = 0 := by
            ring_nf
  exact (Complex.sub_real_mul_I_ne_zero_of_re_pos hw_re_pos) hzero

/-- For `t > 0` and `0 < w.re`, the Cayley transform appearing in the
principal-log definition of `Complex.arctan ((t : ℂ) / w)` lies in the slit
plane, so the principal logarithm is differentiable there. -/
theorem Complex.binet_arctan_log_argument_mem_slitPlane
    {t : ℝ} {w : ℂ}
    (ht : 0 < t)
    (hw_re_pos : 0 < w.re) :
    (1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I) ∈ Complex.slitPlane := by
  sorry

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
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_inv hw_ne).const_mul (t : ℂ)
  have h_outer :
      HasDerivAt
        Complex.arctan
        ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) ((t : ℂ) / w) :=
    Complex.arctan_hasDerivAt_of_log_argument_mem_slitPlane
      harg_ne_I harg_ne_negI harg_slit
  have hcomp :
      HasDerivAt
        (fun z : ℂ => Complex.arctan ((t : ℂ) / z))
        (((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2)) w := by
    simpa [Function.comp_def] using h_outer.comp w h_inner
  have hden_ne : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 :=
    Complex.binet_arctan_derivative_denominator_ne_zero hw_re_pos
  have halg :
      ((1 : ℂ) / (1 + ((t : ℂ) / w) ^ 2)) *
          (-(t : ℂ) / w ^ 2) =
        -(t : ℂ) / (w ^ 2 + (t : ℂ) ^ 2) := by
    field_simp [hw_ne, hden_ne]
    ring
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
  simpa [Complex.binetSecondFormulaDerivativeKernel] using
    (Complex.arctan_t_div_hasDerivAt ht hw_re_pos).div_const
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- A small ball around a point in the open right half-plane remains in the
open right half-plane. -/
theorem Complex.exists_ball_subset_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : ℂ, ‖z - w‖ < ε → 0 < z.re := by
  refine ⟨w.re / 2, half_pos hw_re_pos, ?_⟩
  intro z hz
  have hre_le_norm : |z.re - w.re| ≤ ‖z - w‖ := by
    simpa [Complex.norm_eq_abs, sub_re] using
      (abs_re_le_abs (z - w))
  have hre_abs_lt : |z.re - w.re| < w.re / 2 :=
    lt_of_le_of_lt hre_le_norm hz
  have hre_lower : -(w.re / 2) < z.re - w.re :=
    (abs_lt.mp hre_abs_lt).1
  have hw_half_pos : 0 < w.re / 2 :=
    half_pos hw_re_pos
  have hhalf_lt_z : w.re / 2 < z.re := by
    calc
      w.re / 2 = w.re + (-(w.re / 2)) := by ring
      _ < w.re + (z.re - w.re) :=
        add_lt_add_left hre_lower w.re
      _ = z.re := by ring
  exact hw_half_pos.trans hhalf_lt_z

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
          ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
            HasDerivAt
              (fun u : ℂ =>
                Complex.arctan ((t : ℂ) / u) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
              (Complex.binetSecondFormulaDerivativeKernel t z) z := by
  rcases Complex.exists_ball_subset_openRightHalfPlane hw_re_pos with
    ⟨ε, hε_pos, hε_subset⟩
  refine ⟨ε, hε_pos, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  exact
    Complex.binetSecondFormula_arctanKernel_hasDerivAt
      ht (hε_subset z hz)

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
  sorry

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
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
              ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t := by
  rcases
    Complex.binetSecondFormula_arctanKernel_derivative_pointwise_majorant
      hw_re_pos with
    ⟨ε, hε_pos, g, hg_int, hg_bound⟩
  refine ⟨ε, hε_pos, g, hg_int, ?_⟩
  intro z hz
  filter_upwards
    [MeasureTheory.self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))]
    with t ht
  exact hg_bound z hz t ht

/-- Integral derivative transport for the Binet second-formula remainder from
the pointwise arctangent-kernel derivative and its local integrable majorant. -/
theorem Complex.binetSecondFormulaRemainder_hasDerivAt_from_kernel_derivative
    {w : ℂ}
    (hkernel :
      ∃ ε : ℝ,
        0 < ε ∧
        ∀ z : ℂ,
          ‖z - w‖ < ε →
            ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
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
          ∀ z : ℂ,
            ‖z - w‖ < ε →
              ∀ᵐ t ∂(Measure.restrict volume (Set.Ioi (0 : ℝ))),
                ‖Complex.binetSecondFormulaDerivativeKernel t z‖ ≤ g t) :
    HasDerivAt
      Complex.binetSecondFormulaRemainder
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  sorry

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
      (Complex.binetSecondFormula_arctanKernel_local_hasDerivAt
        hw_re_pos)
      (Complex.binetSecondFormula_arctanKernel_derivative_locally_dominated
        hw_re_pos)

/-- The missing special-function derivative identity behind Binet's second
formula: the logarithmic derivative of Gamma minus the derivative of the
explicit Binet main term is the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  sorry

/-- The logarithmic Gamma side and explicit Binet main term have the
derivative prescribed by the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder_from_digamma_Binet
      hw_re_pos

/-- The logarithmic Gamma side, after subtracting the explicit Binet main
term, has derivative equal to the differentiated Binet remainder. -/
theorem Complex.Gamma_logGamma_sub_binetMainTerm_hasDerivAt_remainderDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          Complex.binetLogGammaMainTerm z)
      (Complex.binetSecondFormulaRemainderDerivative w) w := by
  exact
    Complex.Gamma_logGamma_sub_binetMainTerm_derivative_matches_remainder
      hw_re_pos

/-- Differentiating the arctangent-kernel integral under the integral sign
gives the same logarithmic derivative as the Gamma side after subtracting the
explicit Binet main term. -/
theorem Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
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
      hw_re_pos
  have hremainder :
      HasDerivAt
        Complex.binetSecondFormulaRemainder
        (Complex.binetSecondFormulaRemainderDerivative w) w :=
    Complex.binetSecondFormulaRemainder_hasDerivAt
      hw_re_pos
  simpa [sub_eq_add_neg, add_assoc] using hlog_main.sub hremainder

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
    simpa [S] using (convex_halfSpace_re_gt (r := 0))
  have hopen : IsOpen S := by
    simpa [S] using
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
    exact
      (hderiv hu).hasFDerivAt.hasFDerivWithinAt.fderivWithin hunique
  exact hconv.is_const_of_fderivWithin_eq_zero hdiff hzero hz hw

/-- The two sides of Binet's second formula have the same complex derivative
on the open right half-plane.

This is the analytic continuation/differentiation root: after differentiating
the arctangent-kernel integral under the integral sign, the derivative agrees
with the logarithmic derivative of `Gamma` minus the derivative of the explicit
main term. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ =>
        Complex.log (Complex.Gamma z) -
          (Complex.binetLogGammaMainTerm z +
            Complex.binetSecondFormulaRemainder z))
      0 w := by
  exact
    Complex.Gamma_binetSecondFormula_arctanKernel_integral_sameDerivative
      hw_re_pos

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
    simpa using hw
  have hconstant : F (w.re : ℂ) = F w :=
    Complex.openRightHalfPlane_eq_of_hasDerivAt_zero
      (F := F)
      (fun hz => hderiv hz)
      hbase_re hw
  have hbase_zero : F (w.re : ℂ) = 0 := by
    dsimp [F]
    exact sub_eq_zero.mpr (hreal hw)
  have hw_zero : F w = 0 := by
    exact Eq.trans hconstant.symm hbase_zero
  exact sub_eq_zero.mp hw_zero

/-- The open right half-plane is connected to the positive real axis by
paths along which the principal-log Binet difference has zero derivative.

This consumes the real-axis normalization and the zero-derivative identity to
propagate Binet's formula through the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_from_realAxis_and_derivative :
    ∀ w : ℂ,
      0 < w.re →
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane_of_positiveReal_and_sameDerivative
      (fun hx =>
        Complex.Gamma_binetSecondFormula_integral_representation_positiveReal
          hx)
      (fun hw_re_pos =>
        Complex.Gamma_binetSecondFormula_integral_representation_sameDerivative
          hw_re_pos)

/-- The classical second Binet integral representation, with the principal
logarithm normalization used by `Complex.binetLogGammaMainTerm` and the
literal arctangent-kernel remainder used in this package. -/
theorem Complex.Gamma_binetSecondFormula_integral_representation_principalLog :
    ∀ w : ℂ,
      0 < w.re →
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
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_integral_representation_principalLog

/-- Binet's second logarithmic formula on the open right half-plane. -/
theorem Complex.Gamma_binetSecondFormula_openRightHalfPlane :
    ∀ w : ℂ,
      0 < w.re →
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
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro w hw_re_pos _hR
  exact
    Complex.Gamma_binetSecondFormula_openRightHalfPlane
      w hw_re_pos

/-- Large-radius Binet formula for the existing principal-arctangent integral.
The hypothesis is open half-plane because the current remainder is the
pointwise kernel integral, not a boundary-value object on the imaginary axis. -/
theorem Complex.Gamma_binetSecondFormula_closedRightHalfPlane_continuation :
    ∃ R : ℝ,
      0 < R ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
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
        Complex.log (Complex.Gamma w) =
          Complex.binetLogGammaMainTerm w +
            Complex.binetSecondFormulaRemainder w := by
  exact
    Complex.Gamma_binetSecondFormula_closedRightHalfPlane_from_open_continuation

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.arctan_series_term_norm_le_geometric
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ ≤
        ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
  intro n
  have hz_nonneg : 0 ≤ ‖z‖ :=
    norm_nonneg z
  have hsq_le_half : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    have hsq_le_quarter : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      sq_le_sq' hz_nonneg hz
    have hquarter_le_half : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) := by
      norm_num
    exact le_trans hsq_le_quarter hquarter_le_half
  have hpow_bound :
      ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
    calc
      ‖z‖ ^ (2 * n + 1) = ‖z‖ * (‖z‖ ^ 2) ^ n := by
        ring
      _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
        exact
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sq_nonneg ‖z‖) hsq_le_half n)
            hz_nonneg
  have hden_ge_one : (1 : ℝ) ≤ ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
    norm_num
  have hden_pos : 0 < ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one hden_ge_one
  have hdiv_le :
      ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ ≤
        ‖z‖ ^ (2 * n + 1) := by
    exact
      div_le_of_le_mul₀
        (norm_nonneg _)
        hden_pos
        (by
          calc
            ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ ^ (2 * n + 1) * 1 := by
              rw [mul_one]
            _ ≤ ‖z‖ ^ (2 * n + 1) * ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hden_ge_one
                (pow_nonneg hz_nonneg (2 * n + 1)))
  calc
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ =
        ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      simp [norm_div, norm_mul, norm_pow]
    _ ≤ ‖z‖ ^ (2 * n + 1) := hdiv_le
    _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := hpow_bound

/-- The geometric majorant for the arctangent series sums to `2 * ‖z‖`. -/
theorem Complex.arctan_geometric_majorant_hasSum
    (z : ℂ) :
    HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) := by
  have hgeom :
      HasSum (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hmul :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n))
        (‖z‖ * (1 - (1 / 2 : ℝ))⁻¹) :=
    hgeom.mul_left ‖z‖
  have hsum_eq :
      ‖z‖ * (1 - (1 / 2 : ℝ))⁻¹ = 2 * ‖z‖ := by
    ring
  exact hsum_eq ▸ hmul

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`, proved from the arctangent power series. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  have hz_lt_one : ‖z‖ < (1 : ℝ) :=
    lt_of_le_of_lt hz (by norm_num : (1 / 2 : ℝ) < 1)
  have hseries :
      HasSum
        (fun n : ℕ =>
          (-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ))
        (Complex.arctan z) :=
    Complex.hasSum_arctan hz_lt_one
  have hmajorant :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) :=
    Complex.arctan_geometric_majorant_hasSum z
  exact
    hseries.norm_le_of_bounded hmajorant
      (Complex.arctan_series_term_norm_le_geometric hz)

/-- Principal arctangent is Lipschitz with constant `2` on the closed disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  exact
    Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series hz

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

/-- Small-argument arctangent bound for the Binet kernel.

The principal arctangent has branch singularities at `±I`, so the honest
pointwise estimate is a small-argument sector estimate, not a global
open-half-plane estimate. -/
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

/-- Strict positivity of the Binet real exponential denominator at every
positive point. -/
theorem Real.binetSecondFormula_exp_denominator_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  have htwo_pi_pos : 0 < (2 : ℝ) * Real.pi :=
    mul_pos two_pos Real.pi_pos
  have hexponent_pos : 0 < (2 : ℝ) * Real.pi * t :=
    mul_pos htwo_pi_pos ht
  have hone_lt_exp :
      1 < Real.exp ((2 : ℝ) * Real.pi * t) := by
    calc
      1 = Real.exp 0 := by
        exact Real.exp_zero.symm
      _ < Real.exp ((2 : ℝ) * Real.pi * t) :=
        Real.exp_lt_exp.mpr hexponent_pos
  exact sub_pos.mpr hone_lt_exp

/-- Positivity removes the norm from the Binet real denominator. -/
theorem Real.binetSecondFormula_exp_denominator_norm_eq
    {t : ℝ}
    (ht : 0 < t) :
    ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ =
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  exact
    Real.norm_of_nonneg
      (le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht))

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
half-plane.

The literal closed-boundary principal-arctangent kernel has singular boundary
values on the imaginary axis, so the pointwise owner estimate stays in the
open half-plane and away from the arctangent branch singularities.  Closed
sector estimates are obtained later by the continued Binet remainder, not by
evaluating this kernel pointwise on the boundary. -/
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

/-- Strict positivity of the Binet majorant denominator at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  exact Real.binetSecondFormula_exp_denominator_pos ht

/-- Nonvanishing of the Binet majorant denominator at every positive point. -/
theorem Real.binetSecondFormula_kernel_majorant_denominator_ne_zero
    {t : ℝ}
    (ht : 0 < t) :
    Real.exp ((2 : ℝ) * Real.pi * t) - 1 ≠ 0 :=
  ne_of_gt
    (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Positivity of the Binet real majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_pos
    {t : ℝ}
    (ht : 0 < t) :
    0 < t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    div_pos ht
      (Real.binetSecondFormula_kernel_majorant_denominator_pos ht)

/-- Nonnegativity of the Binet real majorant on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  intro t ht
  exact le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht)

/-- Exponential lower bound giving cancellation of the zero of
`exp (2πt) - 1` at the origin. -/
theorem Real.two_pi_mul_le_exp_two_pi_mul_sub_one
    {t : ℝ}
    (ht : 0 ≤ t) :
    (2 : ℝ) * Real.pi * t ≤
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  let x : ℝ := (2 : ℝ) * Real.pi * t
  have hx_nonneg : 0 ≤ x :=
    mul_nonneg (le_of_lt (mul_pos two_pos Real.pi_pos)) ht
  have hlower : x + 1 ≤ Real.exp x :=
    Real.add_one_le_exp x
  change x ≤ Real.exp x - 1
  linarith

/-- Division form of the zero-cancellation estimate for the Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_le_one_div_two_pi
    {t : ℝ}
    (ht : 0 < t) :
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      1 / ((2 : ℝ) * Real.pi) := by
  let a : ℝ := (2 : ℝ) * Real.pi
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have ha_pos : 0 < a :=
    mul_pos two_pos Real.pi_pos
  have hd_pos : 0 < d :=
    Real.binetSecondFormula_kernel_majorant_denominator_pos ht
  have had_le : a * t ≤ d := by
    exact Real.two_pi_mul_le_exp_two_pi_mul_sub_one (le_of_lt ht)
  have hmul : a * (t / d) ≤ 1 := by
    have hle_div : a * t / d ≤ d / d :=
      div_le_div_of_nonneg_right had_le (le_of_lt hd_pos)
    have hd_div : d / d = 1 :=
      div_self (ne_of_gt hd_pos)
    calc
      a * (t / d) = a * t / d := by ring
      _ ≤ d / d := hle_div
      _ = 1 := hd_div
  have hdiv :
      t / d ≤ 1 / a := by
    exact (le_div_iff₀ ha_pos).mpr hmul
  exact hdiv

/-- Pointwise zero-cancellation bound for the Binet majorant on `(0,1]`.

The analytic root is the elementary inequality
`t / (exp (2πt) - 1) ≤ 1 / (2π)`, obtained from
`1 + 2πt ≤ exp (2πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise
    {t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      1 / ((2 : ℝ) * Real.pi) := by
  have hpos :
      0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht.1)
  have hle :
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        1 / ((2 : ℝ) * Real.pi) :=
    Real.binetSecondFormula_kernel_majorant_le_one_div_two_pi ht.1
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1 / ((2 : ℝ) * Real.pi))
      (Real.norm_of_nonneg hpos).symm
      hle

/-- The Binet majorant is bounded near zero after cancellation of the simple
zero in `exp (2πt)-1`. -/
theorem Real.binetSecondFormula_kernel_majorant_bounded_zero_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioc (0 : ℝ) 1 →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤ C := by
  refine ⟨1 / ((2 : ℝ) * Real.pi), ?_, ?_⟩
  · exact one_div_pos.mpr (mul_pos two_pos Real.pi_pos)
  · intro t ht
    exact
      Real.binetSecondFormula_kernel_majorant_zero_cancellation_pointwise ht

/-- A bounded a.e.-measurable real function on a finite interval is integrable. -/
theorem Real.integrableOn_Ioc_of_aestronglyMeasurable_norm_le_const
    {f : ℝ → ℝ}
    {a b C : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioc a b)))
    (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, x ∈ Set.Ioc a b → ‖f x‖ ≤ C) :
    IntegrableOn f (Set.Ioc a b) := by
  refine ⟨hmeas, ?_⟩
  exact
    hasFiniteIntegral_restrict_of_bounded
      (μ := volume)
      (s := Set.Ioc a b)
      (C := C)
      measure_Ioc_lt_top
      ((ae_restrict_mem measurableSet_Ioc).mono
        (fun x hx => hbound x hx))

/-- The Binet majorant is a.e.-measurable on the local interval `(0,1]`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_zero_one :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  have hmeas :
      Measurable
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    fun_prop
  exact hmeas.aestronglyMeasurable

/-- A bounded Binet majorant on `(0,1]` is integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_from_zero_cancellation :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  rcases
      Real.binetSecondFormula_kernel_majorant_bounded_zero_one with
    ⟨C, hC_pos, hC_bound⟩
  exact
    Real.integrableOn_Ioc_of_aestronglyMeasurable_norm_le_const
      Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_zero_one
      (le_of_lt hC_pos)
      hC_bound

/-- The Binet real majorant is integrable near zero. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one_from_zero_cancellation

/-- On the Binet tail, `exp (2πt) - 1` is bounded below by
`(1/2) exp (2πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_denominator_lower
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    (Real.exp ((2 : ℝ) * Real.pi * t)) / 2 ≤
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  let x : ℝ := (2 : ℝ) * Real.pi * t
  have hx_ge_two_pi : (2 : ℝ) * Real.pi ≤ x := by
    have hcoeff_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
      le_of_lt (mul_pos two_pos Real.pi_pos)
    calc
      (2 : ℝ) * Real.pi = (2 : ℝ) * Real.pi * 1 := by ring
      _ ≤ (2 : ℝ) * Real.pi * t :=
        mul_le_mul_of_nonneg_left (le_of_lt ht) hcoeff_nonneg
      _ = x := rfl
  have hlog_two_le_two_pi : Real.log 2 ≤ (2 : ℝ) * Real.pi := by
    have hlog_two_lt_two : Real.log 2 < (2 : ℝ) := by
      exact Real.log_lt_self (by norm_num : (1 : ℝ) < 2)
    exact le_trans (le_of_lt hlog_two_lt_two) (le_of_lt (by positivity : (2 : ℝ) < 2 * Real.pi))
  have hlog_two_le_x : Real.log 2 ≤ x :=
    le_trans hlog_two_le_two_pi hx_ge_two_pi
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp x := by
    have htwo_pos : (0 : ℝ) < 2 := by norm_num
    exact (Real.log_le_iff_le_exp htwo_pos).mp hlog_two_le_x
  change Real.exp x / 2 ≤ Real.exp x - 1
  nlinarith [Real.exp_pos x]

/-- The linear factor on the Binet tail is absorbed by `exp (πt)`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_linear_le_exp_pi
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    t ≤ Real.exp (Real.pi * t) := by
  have ht_nonneg : 0 ≤ t :=
    le_of_lt (lt_trans zero_lt_one ht)
  have hpi_t_ge_t : t ≤ Real.pi * t := by
    have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
      le_of_lt Real.one_lt_pi
    calc
      t = 1 * t := by ring
      _ ≤ Real.pi * t :=
        mul_le_mul_of_nonneg_right hone_le_pi ht_nonneg
  have ht_le_add : t ≤ Real.pi * t + 1 :=
    le_trans hpi_t_ge_t (le_add_of_nonneg_right zero_le_one)
  have hadd_le_exp : Real.pi * t + 1 ≤ Real.exp (Real.pi * t) :=
    Real.add_one_le_exp (Real.pi * t)
  exact le_trans ht_le_add hadd_le_exp

/-- Pointwise tail domination after separating the denominator lower bound
and the linear/exponential absorption. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_two_exp_of_denominator_lower
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      2 * Real.exp (-Real.pi * t) := by
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t)
  let d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hE_pos : 0 < E :=
    Real.exp_pos ((2 : ℝ) * Real.pi * t)
  have hd_pos : 0 < d :=
    Real.binetSecondFormula_kernel_majorant_denominator_pos
      (lt_trans zero_lt_one ht)
  have hd_lower : E / 2 ≤ d :=
    Real.binetSecondFormula_kernel_majorant_tail_denominator_lower ht
  have ht_le_exp : t ≤ Real.exp (Real.pi * t) :=
    Real.binetSecondFormula_kernel_majorant_tail_linear_le_exp_pi ht
  have hdiv_le : t / d ≤ t / (E / 2) :=
    div_le_div_of_nonneg_left
      (le_of_lt (lt_trans zero_lt_one ht))
      (div_pos hE_pos two_pos)
      hd_lower
  have hrewrite : t / (E / 2) = 2 * (t / E) := by
    field_simp [hE_pos.ne']
  have ht_over_E_le :
      t / E ≤ Real.exp (-Real.pi * t) := by
    have hmul_le :
        t ≤ E * Real.exp (-Real.pi * t) := by
      calc
        t ≤ Real.exp (Real.pi * t) := ht_le_exp
        _ = E * Real.exp (-Real.pi * t) := by
          simp [E, ← Real.exp_add]
          ring_nf
    exact (div_le_iff₀ hE_pos).mpr hmul_le
  calc
    t / d ≤ t / (E / 2) := hdiv_le
    _ = 2 * (t / E) := hrewrite
    _ ≤ 2 * Real.exp (-Real.pi * t) :=
      mul_le_mul_of_nonneg_left ht_over_E_le (by norm_num : (0 : ℝ) ≤ 2)

/-- Pointwise exponential tail domination for the Binet majorant with the
concrete constant `2`. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp
    {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
      2 * Real.exp (-Real.pi * t) := by
  have ht_pos : 0 < t :=
    lt_trans zero_lt_one ht
  have hnonneg :
      0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    le_of_lt (Real.binetSecondFormula_kernel_majorant_pos ht_pos)
  have hle :
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        2 * Real.exp (-Real.pi * t) :=
    Real.binetSecondFormula_kernel_majorant_tail_le_two_exp_of_denominator_lower ht
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2 * Real.exp (-Real.pi * t))
      (Real.norm_of_nonneg hnonneg).symm
      hle

/-- The Binet real majorant has an exponentially decaying tail. -/
theorem Real.binetSecondFormula_kernel_majorant_tail_le_exp :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (1 : ℝ) →
          ‖t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)‖ ≤
            C * Real.exp (-Real.pi * t) := by
  refine ⟨2, two_pos, ?_⟩
  intro t ht
  exact
    Real.binetSecondFormula_kernel_majorant_tail_pointwise_le_two_exp ht

/-- A real function dominated on a tail by a decaying exponential is integrable
on that tail. -/
theorem Real.integrableOn_Ioi_of_aestronglyMeasurable_norm_le_exp_tail
    {f : ℝ → ℝ}
    {a C b : ℝ}
    (hmeas : AEStronglyMeasurable f (volume.restrict (Set.Ioi a)))
    (hC : 0 ≤ C)
    (hb : 0 < b)
    (hbound :
      ∀ t : ℝ,
        t ∈ Set.Ioi a →
          ‖f t‖ ≤ C * Real.exp (-b * t)) :
    IntegrableOn f (Set.Ioi a) := by
  have h_exp :
      IntegrableOn (fun t : ℝ => Real.exp (-b * t)) (Set.Ioi a) :=
    exp_neg_integrableOn_Ioi a hb
  have h_bound_integrable :
      Integrable (fun t : ℝ => C * Real.exp (-b * t))
        (volume.restrict (Set.Ioi a)) :=
    h_exp.integrable.const_mul C
  exact
    h_bound_integrable.mono'
      hmeas
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => hbound t ht))

/-- The Binet majorant is a.e.-measurable on the tail interval `(1,∞)`. -/
theorem Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_one_infty :
    AEStronglyMeasurable
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
    fun_prop
  exact hmeas.aestronglyMeasurable

/-- Exponential tail domination implies tail integrability of the Binet
majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_from_exponential_tail :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  rcases
      Real.binetSecondFormula_kernel_majorant_tail_le_exp with
    ⟨C, hC_pos, hC_bound⟩
  exact
    Real.integrableOn_Ioi_of_aestronglyMeasurable_norm_le_exp_tail
      Real.binetSecondFormula_kernel_majorant_aestronglyMeasurableOn_one_infty
      (le_of_lt hC_pos)
      Real.pi_pos
      hC_bound

/-- The Binet real majorant is integrable at infinity. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (1 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty_from_exponential_tail

/-- The positive half-line decomposes into the local Binet interval `(0,1]`
and the tail interval `(1,∞)`. -/
theorem Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one :
    Set.Ioi (0 : ℝ) =
      Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) := by
  exact
    Set.ext
      (fun x =>
        ⟨fun hx =>
            Or.elim (lt_or_ge (1 : ℝ) x)
              (fun hone_lt_x => Or.inr hone_lt_x)
              (fun hx_le_one => Or.inl ⟨hx, hx_le_one⟩),
          fun hx =>
            Or.elim hx
              (fun hx_local => hx_local.1)
              (fun hx_tail => lt_trans zero_lt_one hx_tail)⟩)

/-- Joining local integrability on `(0,1]` with tail integrability on `(1,∞)`
gives integrability on `(0,∞)`. -/
theorem Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
    {f : ℝ → ℝ}
    (hlocal : IntegrableOn f (Set.Ioc (0 : ℝ) 1))
    (htail : IntegrableOn f (Set.Ioi (1 : ℝ))) :
    IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  have hcover :
      Set.Ioi (0 : ℝ) =
        Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) :=
    Real.Ioi_zero_eq_Ioc_zero_one_union_Ioi_one
  have hunion :
      IntegrableOn f (Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ)) :=
    integrableOn_union.mpr ⟨hlocal, htail⟩
  exact
    Eq.subst
      (motive := fun s : Set ℝ => IntegrableOn f s)
      hcover.symm
      hunion

/-- The real majorant for the Binet kernel is integrable on `(0,∞)` once its
local and tail pieces are integrable. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
    (hlocal :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioc (0 : ℝ) 1))
    (htail :
      IntegrableOn
        (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Ioi (1 : ℝ))) :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.integrableOn_Ioi_zero_of_Ioc_zero_one_and_Ioi_one
      hlocal htail

/-- The Binet real majorant is integrable on the positive half-line. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioi (0 : ℝ)) := by
  exact
    Real.binetSecondFormula_kernel_majorant_integrableOn_from_zero_local_and_infinity
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_one_infty

end

end LFunctions
end Boundary
