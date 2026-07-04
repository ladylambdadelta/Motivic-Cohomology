import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.BranchIntegral.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Denominator.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet.Derivatives.Owner

/-!
# Holomorphy of the Binet second-formula derivative kernel

The differentiated Binet remainder integrand
`binetSecondFormulaDerivativeKernel t w = (-(t)/(w^2 + t^2)) / (exp(2πt) - 1)`
is, for each fixed real `t`, a holomorphic function of `w` on the open right
half-plane `0 < w.re`.  The only obstruction is the zero set of the denominator
`w^2 + t^2`, which lies on the imaginary axis (`w = ± t·I`); it is avoided
whenever `0 < w.re`.

This is the pointwise-in-`t` holomorphy foundation for the vertical line-shift
Cauchy argument that the archimedean Binet-remainder leaves require.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The Binet denominator `w^2 + t^2` is nonzero on the open right half-plane.

It factors as `(w + t·I)(w - t·I)`; each factor has real part `w.re`, so for
`0 < w.re` neither factor vanishes. -/
theorem Complex.binetSecondFormula_sq_add_sq_ne_zero_of_re_pos
    (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    w ^ 2 + (t : ℂ) ^ 2 ≠ 0 := by
  have hfactor :
      (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) =
        w ^ 2 + (t : ℂ) ^ 2 :=
    Complex.add_mul_I_mul_sub_mul_I_eq_sq_add_sq w t
  have hadd : w + (t : ℂ) * Complex.I ≠ 0 := by
    intro hz
    have hre : (w + (t : ℂ) * Complex.I).re = (0 : ℂ).re :=
      congrArg Complex.re hz
    have hleft : (w + (t : ℂ) * Complex.I).re = w.re := by
      calc
        (w + (t : ℂ) * Complex.I).re =
            w.re + ((t : ℂ) * Complex.I).re :=
          Complex.add_re w ((t : ℂ) * Complex.I)
        _ = w.re + -((t : ℂ).im) :=
          congrArg (fun y : ℝ => w.re + y) (Complex.mul_I_re (t : ℂ))
        _ = w.re + -0 :=
          congrArg (fun y : ℝ => w.re + -y) (Complex.ofReal_im t)
        _ = w.re + 0 :=
          congrArg (fun y : ℝ => w.re + y) (neg_zero : -(0 : ℝ) = 0)
        _ = w.re := add_zero w.re
    have hw_re_zero : w.re = 0 :=
      (hleft.symm.trans hre).trans Complex.zero_re
    exact hw.ne' hw_re_zero
  have hsub : w - (t : ℂ) * Complex.I ≠ 0 := by
    intro hz
    have hre : (w - (t : ℂ) * Complex.I).re = (0 : ℂ).re :=
      congrArg Complex.re hz
    have hleft : (w - (t : ℂ) * Complex.I).re = w.re := by
      calc
        (w - (t : ℂ) * Complex.I).re =
            w.re - ((t : ℂ) * Complex.I).re :=
          Complex.sub_re w ((t : ℂ) * Complex.I)
        _ = w.re - -((t : ℂ).im) :=
          congrArg (fun y : ℝ => w.re - y) (Complex.mul_I_re (t : ℂ))
        _ = w.re - -0 :=
          congrArg (fun y : ℝ => w.re - -y) (Complex.ofReal_im t)
        _ = w.re - 0 :=
          congrArg (fun y : ℝ => w.re - y) (neg_zero : -(0 : ℝ) = 0)
        _ = w.re := sub_zero w.re
    have hw_re_zero : w.re = 0 :=
      (hleft.symm.trans hre).trans Complex.zero_re
    exact hw.ne' hw_re_zero
  have hprod : (w + (t : ℂ) * Complex.I) * (w - (t : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero hadd hsub
  exact hfactor ▸ hprod

/-- For each fixed real `t`, the Binet second-formula derivative kernel is
complex-differentiable at every point of the open right half-plane. -/
theorem Complex.binetSecondFormulaDerivativeKernel_differentiableAt_of_re_pos
    (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ
      (fun z : ℂ => Complex.binetSecondFormulaDerivativeKernel t z) w := by
  have hdenom :
      DifferentiableAt ℂ (fun z : ℂ => z ^ 2 + (t : ℂ) ^ 2) w :=
    (differentiableAt_id.pow 2).add (differentiableAt_const _)
  have hne : (fun z : ℂ => z ^ 2 + (t : ℂ) ^ 2) w ≠ 0 :=
    Complex.binetSecondFormula_sq_add_sq_ne_zero_of_re_pos t hw
  have hfrac :
      DifferentiableAt ℂ
        (fun z : ℂ => -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2)) w :=
    (differentiableAt_const _).div hdenom hne
  exact hfrac.div_const
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- Explicit complex derivative of the Binet second-formula derivative kernel in
`w` on the open right half-plane.

The derivative value `2·t·w / (w^2 + t^2)^2 / (exp(2πt) - 1)` is the form used for
the domination estimate in the differentiation-under-the-integral step. -/
theorem Complex.binetSecondFormulaDerivativeKernel_hasDerivAt_of_re_pos
    (t : ℝ) {w : ℂ} (hw : 0 < w.re) :
    HasDerivAt
      (fun z : ℂ => Complex.binetSecondFormulaDerivativeKernel t z)
      ((2 * (t : ℂ) * w / (w ^ 2 + (t : ℂ) ^ 2) ^ 2) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) w := by
  have hne : w ^ 2 + (t : ℂ) ^ 2 ≠ 0 :=
    Complex.binetSecondFormula_sq_add_sq_ne_zero_of_re_pos t hw
  -- derivative of the denominator `z ↦ z^2 + t^2`
  have hpow : HasDerivAt (fun z : ℂ => z ^ 2) (2 * w) w := by
    have h0 : HasDerivAt (fun z : ℂ => z ^ 2)
        ((2 : ℂ) * w ^ (2 - 1)) w := by
      exact hasDerivAt_pow 2 w
    have hexp : w ^ (2 - 1) = w := pow_one w
    exact (congrArg (fun s : ℂ => (2 : ℂ) * s) hexp) ▸ h0
  have hd : HasDerivAt (fun z : ℂ => z ^ 2 + (t : ℂ) ^ 2) (2 * w) w :=
    hpow.add_const _
  have hc : HasDerivAt (fun _ : ℂ => -(t : ℂ)) 0 w := hasDerivAt_const w _
  -- raw quotient derivative, then reconcile the numerator explicitly
  have hraw :
      HasDerivAt (fun z : ℂ => -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2))
        ((0 * (w ^ 2 + (t : ℂ) ^ 2) - -(t : ℂ) * (2 * w)) /
          (w ^ 2 + (t : ℂ) ^ 2) ^ 2) w :=
    hc.div hd hne
  have hnum :
      0 * (w ^ 2 + (t : ℂ) ^ 2) - -(t : ℂ) * (2 * w) =
        2 * (t : ℂ) * w := by
    calc
      0 * (w ^ 2 + (t : ℂ) ^ 2) - -(t : ℂ) * (2 * w)
          = 0 - -(t : ℂ) * (2 * w) := by
            exact congrArg (fun s : ℂ => s - -(t : ℂ) * (2 * w))
              (zero_mul (w ^ 2 + (t : ℂ) ^ 2))
      _ = -(-(t : ℂ) * (2 * w)) := zero_sub _
      _ = -(-((t : ℂ) * (2 * w))) :=
            congrArg Neg.neg (neg_mul (t : ℂ) (2 * w))
      _ = (t : ℂ) * (2 * w) := neg_neg _
      _ = 2 * ((t : ℂ) * w) := mul_left_comm (t : ℂ) 2 w
      _ = 2 * (t : ℂ) * w := (mul_assoc 2 (t : ℂ) w).symm
  have hdiv :
      HasDerivAt (fun z : ℂ => -(t : ℂ) / (z ^ 2 + (t : ℂ) ^ 2))
        (2 * (t : ℂ) * w / (w ^ 2 + (t : ℂ) ^ 2) ^ 2) w :=
    (congrArg (fun s : ℂ => s / (w ^ 2 + (t : ℂ) ^ 2) ^ 2) hnum) ▸ hraw
  exact hdiv.div_const
    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- Numerator norm bound `‖2·t·z‖ ≤ 2·R·t` on a norm-bounded set, for `t > 0`. -/
theorem Complex.binetSecondFormula_deriv_numerator_norm_le
    {z : ℂ} {R t : ℝ} (hz_le : ‖z‖ ≤ R) (ht : 0 < t) :
    ‖2 * (t : ℂ) * z‖ ≤ 2 * R * t := by
  have h2 : ‖(2 : ℂ)‖ = 2 := Complex.norm_ofNat 2
  have htnorm : ‖(t : ℂ)‖ = t := by
    calc
      ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
      _ = t := abs_of_pos ht
  have hstep :
      ‖2 * (t : ℂ) * z‖ = 2 * t * ‖z‖ := by
    calc
      ‖2 * (t : ℂ) * z‖ = ‖2 * (t : ℂ)‖ * ‖z‖ := norm_mul _ _
      _ = ‖(2 : ℂ)‖ * ‖(t : ℂ)‖ * ‖z‖ := by
        exact congrArg (fun x : ℝ => x * ‖z‖) (norm_mul _ _)
      _ = 2 * t * ‖z‖ := by
        exact congrArg₂ (fun a b : ℝ => a * b * ‖z‖) h2 htnorm
  have hzR : 2 * t * ‖z‖ ≤ 2 * t * R :=
    mul_le_mul_of_nonneg_left hz_le
      (mul_nonneg zero_le_two ht.le)
  calc
    ‖2 * (t : ℂ) * z‖ = 2 * t * ‖z‖ := hstep
    _ ≤ 2 * t * R := hzR
    _ = 2 * R * t := by
      calc
        2 * t * R = 2 * (t * R) := mul_assoc 2 t R
        _ = 2 * (R * t) := congrArg (fun y : ℝ => 2 * y) (mul_comm t R)
        _ = 2 * R * t := (mul_assoc 2 R t).symm

/-- Domination bound for the `w`-derivative of the Binet derivative kernel on a
right-half-plane ball of real-part margin `δ` and radius bound `R`: it is
dominated by the integrable majorant `(2R/δ^4)·(t/(exp(2πt)-1))`. -/
theorem Complex.binetSecondFormulaDerivativeKernel_deriv_norm_le_scaled_majorant
    {z : ℂ} {δ R t : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_re : δ ≤ z.re) (hz_le : ‖z‖ ≤ R) (ht : 0 < t) :
    ‖(2 * (t : ℂ) * z / (z ^ 2 + (t : ℂ) ^ 2) ^ 2) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      (2 * R / δ ^ 4) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  set D : ℂ := z ^ 2 + (t : ℂ) ^ 2 with hD
  set d : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1 with hd
  have hd_pos : 0 < d := Real.binetSecondFormula_exp_denominator_pos ht
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ = d := by
    calc
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
          ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
        Complex.binetSecondFormula_exp_denominator_norm_eq t
      _ = d := Real.binetSecondFormula_exp_denominator_norm_eq ht
  -- lower bound on the squared denominator
  have hlow : δ ^ 2 ≤ ‖D‖ :=
    Complex.binet_arctan_derivative_denominator_norm_lower hδ_pos.le hδ_le_re
  have hDsq_ge : δ ^ 4 ≤ ‖D‖ ^ 2 := by
    have h := pow_le_pow_left (sq_nonneg δ) hlow 2
    calc
      δ ^ 4 = δ ^ (2 * 2) := rfl
      _ = (δ ^ 2) ^ 2 := pow_mul δ 2 2
      _ ≤ ‖D‖ ^ 2 := h
  have hδ4_pos : 0 < δ ^ 4 := pow_pos hδ_pos 4
  have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg z) hz_le
  have h2Rt_nonneg : 0 ≤ 2 * R * t :=
    mul_nonneg (mul_nonneg zero_le_two hR_nonneg) ht.le
  -- numerator bound
  have hnum : ‖2 * (t : ℂ) * z‖ ≤ 2 * R * t :=
    Complex.binetSecondFormula_deriv_numerator_norm_le hz_le ht
  have hfrac_le : ‖2 * (t : ℂ) * z / D ^ 2‖ ≤ 2 * R * t / δ ^ 4 := by
    have hsplit : ‖2 * (t : ℂ) * z / D ^ 2‖ = ‖2 * (t : ℂ) * z‖ / ‖D‖ ^ 2 := by
      calc
        ‖2 * (t : ℂ) * z / D ^ 2‖ =
            ‖2 * (t : ℂ) * z‖ / ‖D ^ 2‖ := norm_div _ _
        _ = ‖2 * (t : ℂ) * z‖ / ‖D‖ ^ 2 :=
          congrArg (fun y : ℝ => ‖2 * (t : ℂ) * z‖ / y) (norm_pow D 2)
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 2 * R * t / δ ^ 4)
        hsplit.symm
        (div_le_div h2Rt_nonneg hnum hδ4_pos hDsq_ge)
  -- assemble through the exponential denominator
  have hkernel_norm :
      ‖(2 * (t : ℂ) * z / D ^ 2) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖2 * (t : ℂ) * z / D ^ 2‖ / d := by
    calc
      ‖(2 * (t : ℂ) * z / D ^ 2) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
          ‖2 * (t : ℂ) * z / D ^ 2‖ /
            ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ :=
        norm_div _ _
      _ = ‖2 * (t : ℂ) * z / D ^ 2‖ / d :=
        congrArg (fun y : ℝ => ‖2 * (t : ℂ) * z / D ^ 2‖ / y) hden_norm
  have hdiv :
      ‖2 * (t : ℂ) * z / D ^ 2‖ / d ≤ (2 * R * t / δ ^ 4) / d :=
    div_le_div_of_nonneg_right hfrac_le hd_pos.le
  have hrearrange :
      (2 * R * t / δ ^ 4) / d = (2 * R / δ ^ 4) * (t / d) := by
    let a : ℝ := 2 * R
    let b : ℝ := δ ^ 4
    have hleft :
        (2 * R * t / δ ^ 4) / d =
          (a * t) * (b⁻¹ * d⁻¹) := by
      calc
        (2 * R * t / δ ^ 4) / d =
            ((a * t) / b) / d := rfl
        _ = ((a * t) * b⁻¹) / d :=
          congrArg (fun y : ℝ => y / d) (div_eq_mul_inv (a * t) b)
        _ = ((a * t) * b⁻¹) * d⁻¹ :=
          div_eq_mul_inv ((a * t) * b⁻¹) d
        _ = (a * t) * (b⁻¹ * d⁻¹) :=
          mul_assoc (a * t) b⁻¹ d⁻¹
    have hright :
        (2 * R / δ ^ 4) * (t / d) =
          (a * t) * (b⁻¹ * d⁻¹) := by
      calc
        (2 * R / δ ^ 4) * (t / d) =
            (a / b) * (t / d) := rfl
        _ = (a * b⁻¹) * (t / d) :=
          congrArg (fun y : ℝ => y * (t / d)) (div_eq_mul_inv a b)
        _ = (a * b⁻¹) * (t * d⁻¹) :=
          congrArg (fun y : ℝ => (a * b⁻¹) * y) (div_eq_mul_inv t d)
        _ = (a * t) * (b⁻¹ * d⁻¹) :=
          mul_mul_mul_comm a b⁻¹ t d⁻¹
    exact hleft.trans hright.symm
  calc
    ‖(2 * (t : ℂ) * z / D ^ 2) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖2 * (t : ℂ) * z / D ^ 2‖ / d := hkernel_norm
    _ ≤ (2 * R * t / δ ^ 4) / d := hdiv
    _ = (2 * R / δ ^ 4) * (t / d) := hrearrange

end

end LFunctions
end Boundary
