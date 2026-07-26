import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.Owner
import Mathlib.Analysis.Complex.Liouville

/-!
# Cauchy logarithmic-derivative bounds

This file owns the generic analytic reduction used by the completed
log-derivative strip-control constructors: a Cauchy derivative estimate plus a
lower bound for the value gives a quantitative logarithmic-derivative estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem norm_div_le_div_of_norm_le_of_le_norm
    {x y : ℂ} {A δ : ℝ}
    (hA : ‖x‖ ≤ A)
    (hδ : 0 < δ)
    (hy : δ ≤ ‖y‖) :
    ‖x / y‖ ≤ A / δ :=
  let hA_nonnegative : 0 ≤ A :=
    le_trans (norm_nonneg x) hA
  let hnorm :
      ‖x / y‖ = ‖x‖ / ‖y‖ :=
    norm_div x y
  let hquot :
      ‖x‖ / ‖y‖ ≤ A / δ :=
    div_le_div₀ hA_nonnegative hA hδ hy
  Eq.subst
    (motive := fun u : ℝ => u ≤ A / δ)
    hnorm.symm
    hquot

theorem real_mul_div_right_assoc
    (A q δ : ℝ) :
    (A * q) / δ = (A / δ) * q :=
  let hfirst :
      (A * q) / δ = (A * q) * δ⁻¹ :=
    div_eq_mul_inv (A * q) δ
  let hsecond :
      (A * q) * δ⁻¹ = A * (q * δ⁻¹) :=
    mul_assoc A q δ⁻¹
  let hthird :
      q * δ⁻¹ = δ⁻¹ * q :=
    mul_comm q δ⁻¹
  let hfourth :
      A * (q * δ⁻¹) = A * (δ⁻¹ * q) :=
    congrArg (fun u : ℝ => A * u) hthird
  let hfifth :
      A * (δ⁻¹ * q) = (A * δ⁻¹) * q :=
    (mul_assoc A δ⁻¹ q).symm
  let hsixth :
      (A * δ⁻¹) * q = (A / δ) * q :=
    congrArg (fun u : ℝ => u * q) (div_eq_mul_inv A δ).symm
  Eq.trans hfirst
    (Eq.trans hsecond
      (Eq.trans hfourth
        (Eq.trans hfifth hsixth)))

theorem norm_logDeriv_le_of_deriv_bound_and_value_lower_bound
    {f : ℂ → ℂ} {z : ℂ} {A δ q : ℝ}
    (hderiv : ‖deriv f z‖ ≤ A * q)
    (hδ : 0 < δ)
    (hvalue : δ ≤ ‖f z‖) :
    ‖deriv f z / f z‖ ≤ (A / δ) * q :=
  let hquot :
      ‖deriv f z / f z‖ ≤ (A * q) / δ :=
    norm_div_le_div_of_norm_le_of_le_norm hderiv hδ hvalue
  let hshape :
      (A * q) / δ = (A / δ) * q :=
    real_mul_div_right_assoc A q δ
  Eq.subst
    (motive := fun u : ℝ => ‖deriv f z / f z‖ ≤ u)
    hshape
    hquot

theorem norm_neg_div_eq_norm_div
    (x y : ℂ) :
    ‖-x / y‖ = ‖x / y‖ :=
  let hneg :
      -x / y = -(x / y) :=
    neg_div y x
  let hnorm :
      ‖-(x / y)‖ = ‖x / y‖ :=
    norm_neg (x / y)
  Eq.trans
    (congrArg (fun u : ℂ => ‖u‖) hneg)
    hnorm

theorem cauchy_deriv_norm_le_of_sphere_bound
    {f : ℂ → ℂ} {z : ℂ} {R C : ℝ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball z R))
    (hC : ∀ w : ℂ, w ∈ Metric.sphere z R → ‖f w‖ ≤ C) :
    ‖deriv f z‖ ≤ C / R :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf hC

theorem cauchy_deriv_polynomial_norm_le_of_sphere_bound
    {f : ℂ → ℂ} {z : ℂ} {R A q : ℝ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball z R))
    (hC : ∀ w : ℂ, w ∈ Metric.sphere z R → ‖f w‖ ≤ A * q) :
    ‖deriv f z‖ ≤ (A / R) * q :=
  let hraw :
      ‖deriv f z‖ ≤ (A * q) / R :=
    cauchy_deriv_norm_le_of_sphere_bound hR hf hC
  let hshape :
      (A * q) / R = (A / R) * q :=
    real_mul_div_right_assoc A q R
  Eq.subst
    (motive := fun u : ℝ => ‖deriv f z‖ ≤ u)
    hshape
    hraw

theorem cauchy_logDeriv_polynomial_norm_le_of_sphere_bound
    {f : ℂ → ℂ} {z : ℂ} {R A δ q : ℝ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (Metric.ball z R))
    (hC : ∀ w : ℂ, w ∈ Metric.sphere z R → ‖f w‖ ≤ A * q)
    (hδ : 0 < δ)
    (hvalue : δ ≤ ‖f z‖) :
    ‖deriv f z / f z‖ ≤ ((A / R) / δ) * q :=
  let hderiv :
      ‖deriv f z‖ ≤ (A / R) * q :=
    cauchy_deriv_polynomial_norm_le_of_sphere_bound hR hf hC
  norm_logDeriv_le_of_deriv_bound_and_value_lower_bound
    hderiv
    hδ
    hvalue

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
