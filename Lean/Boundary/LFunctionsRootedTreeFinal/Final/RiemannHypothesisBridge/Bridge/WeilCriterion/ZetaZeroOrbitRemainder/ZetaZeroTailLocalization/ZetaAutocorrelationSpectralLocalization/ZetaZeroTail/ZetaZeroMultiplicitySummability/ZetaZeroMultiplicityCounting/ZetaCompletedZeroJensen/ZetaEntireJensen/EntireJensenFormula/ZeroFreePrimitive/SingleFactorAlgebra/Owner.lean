import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.CauchyMean.Owner

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Boundary factorization for a single nonzero Jensen zero inside the circle. -/
theorem entireFunction_singleZeroFactor_boundary_point_ne_zero
    {ρ : ℝ}
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 := by
  have hρ_ne : (ρ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hexp_ne : Complex.exp (θ * Complex.I) ≠ 0 :=
    Complex.exp_ne_zero (θ * Complex.I)
  exact mul_ne_zero hρ_ne hexp_ne

/-- The inner single-zero boundary factor is nonzero when the zero is strictly
inside the Jensen circle. -/
theorem entireFunction_singleZeroFactor_inner_ne_zero
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hz_ne :
      ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  intro hzero
  have hdiv_eq_one : a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm_div_eq_one :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = 1 :=
    Eq.trans (congrArg norm hdiv_eq_one) norm_one
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_z :
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ρ := by
    calc
      ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
        exact norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I))
      _ = |ρ| * 1 := by
        exact congrArg₂
          (fun x y : ℝ => x * y)
          (Complex.norm_real ρ)
          hnorm_exp
      _ = ρ := by
        exact Eq.trans (mul_one |ρ|) (abs_of_pos hρ_pos)
  have hnorm_a_div :
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ = ‖a‖ / ρ := by
    calc
      ‖a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ =
          ‖a‖ / ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ := by
        exact norm_div a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) hnorm_z
  have hratio_lt_one : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  have hratio_eq_one : ‖a‖ / ρ = 1 :=
    Eq.trans hnorm_a_div.symm hnorm_div_eq_one
  exact (ne_of_lt hratio_lt_one) hratio_eq_one

/-- Boundary factorization for a single nonzero Jensen zero on a nonzero
circle. -/
theorem entireFunction_singleZeroFactor_boundary_factorization
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) =
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
        (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))) := by
  let z : ℂ := (ρ : ℂ) * Complex.exp (θ * Complex.I)
  have hz0 : z ≠ 0 :=
    entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
  have ha_inv : a * a⁻¹ = 1 :=
    mul_inv_cancel₀ ha0
  have hz_inv : z * z⁻¹ = 1 :=
    mul_inv_cancel₀ hz0
  have hinner :
      (z * a⁻¹) * (a * z⁻¹) = 1 := by
    calc
      (z * a⁻¹) * (a * z⁻¹) = ((z * a⁻¹) * a) * z⁻¹ := by
        exact (mul_assoc (z * a⁻¹) a z⁻¹).symm
      _ = (z * (a⁻¹ * a)) * z⁻¹ := by
        exact congrArg (fun x : ℂ => x * z⁻¹) (mul_assoc z a⁻¹ a)
      _ = z * ((a⁻¹ * a) * z⁻¹) := by
        exact mul_assoc z (a⁻¹ * a) z⁻¹
      _ = z * (1 * z⁻¹) := by
        exact congrArg (fun x : ℂ => z * (x * z⁻¹)) (inv_mul_cancel₀ ha0)
      _ = z * z⁻¹ := by
        exact congrArg (fun x : ℂ => z * x) (one_mul z⁻¹)
      _ = 1 := hz_inv
  calc
    1 - (z / a) = 1 - (z * a⁻¹) := by
      exact congrArg (fun x : ℂ => 1 - x) (div_eq_mul_inv z a)
    _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
      calc
        1 - (z * a⁻¹) = 1 - (z * a⁻¹) * 1 := by
          exact congrArg (fun x : ℂ => 1 - x) (mul_one (z * a⁻¹)).symm
        _ =
            (z * a⁻¹) * (a * z⁻¹) - (z * a⁻¹) * 1 := by
          exact congrArg (fun x : ℂ => x - (z * a⁻¹) * 1) hinner.symm
        _ = (z * a⁻¹) * ((a * z⁻¹) - 1) := by
          exact (mul_sub (z * a⁻¹) (a * z⁻¹) 1).symm
        _ = -(z * a⁻¹) * (1 - a * z⁻¹) := by
          let u : ℂ := z * a⁻¹
          let v : ℂ := 1 - a * z⁻¹
          have hsub : (a * z⁻¹) - 1 = -v :=
            (neg_sub 1 (a * z⁻¹)).symm
          have hmul_neg : u * (-v) = -(u * v) :=
            mul_neg u v
          have hneg_mul : -(u * v) = (-u) * v :=
            (neg_mul u v).symm
          exact Eq.trans
            (congrArg (fun y : ℂ => u * y) hsub)
            (Eq.trans hmul_neg hneg_mul)
    _ = -(z / a) * (1 - (a / z)) := by
      exact congrArg₂ (fun x y : ℂ => -x * (1 - y))
        (div_eq_mul_inv z a).symm
        (div_eq_mul_inv a z).symm

/-- The boundary factor has norm `ρ / ‖a‖`. -/
theorem entireFunction_singleZeroFactor_outer_norm
    {a : ℂ}
    {ρ : ℝ}
    (_ha0 : a ≠ 0)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      ρ / ‖a‖ := by
  have hnorm_exp :
      ‖Complex.exp (θ * Complex.I)‖ = 1 := by
    calc
      ‖Complex.exp (θ * Complex.I)‖ =
          Complex.abs (Complex.exp (θ * Complex.I)) := by
        exact Complex.norm_eq_abs (Complex.exp (θ * Complex.I))
      _ = 1 := by
        exact Complex.abs_exp_ofReal_mul_I θ
  have hnorm_rho :
      ‖(ρ : ℂ)‖ = ρ := by
    calc
      ‖(ρ : ℂ)‖ = |ρ| := by
        exact Complex.norm_real ρ
      _ = ρ :=
        abs_of_pos hρ_pos
  calc
    ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
        ‖(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ := by
      exact norm_neg (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)
    _ = ‖((ρ : ℂ) * Complex.exp (θ * Complex.I))‖ / ‖a‖ := by
      exact norm_div ((ρ : ℂ) * Complex.exp (θ * Complex.I)) a
    _ = (‖(ρ : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (norm_mul (ρ : ℂ) (Complex.exp (θ * Complex.I)))
    _ = (ρ * 1) / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖)
        (congrArg₂ (fun x y : ℝ => x * y) hnorm_rho hnorm_exp)
    _ = ρ / ‖a‖ := by
      exact congrArg (fun x : ℝ => x / ‖a‖) (mul_one ρ)

/-- Splitting the logarithm of one boundary factor into the constant outer
radial term and the inner disk logarithmic term. -/
theorem entireFunction_singleZeroFactor_boundary_log_split
    {a : ℂ}
    {ρ : ℝ}
    (ha0 : a ≠ 0)
    (haρ : ‖a‖ < ρ)
    (hρ_pos : 0 < ρ)
    (θ : ℝ) :
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
  have hfactor :=
    entireFunction_singleZeroFactor_boundary_factorization ha0 hρ_pos θ
  have houter_norm :=
    entireFunction_singleZeroFactor_outer_norm ha0 hρ_pos θ
  have hinner_ne :
      1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) ≠ 0 :=
    entireFunction_singleZeroFactor_inner_ne_zero haρ θ
  have houter_ne :
      -(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) ≠ 0 := by
    have hz_ne :
        ((ρ : ℂ) * Complex.exp (θ * Complex.I)) ≠ 0 :=
      entireFunction_singleZeroFactor_boundary_point_ne_zero hρ_pos θ
    exact neg_ne_zero.mpr (div_ne_zero hz_ne ha0)
  have houter_norm_ne :
      ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr houter_ne
  have hinner_norm_ne :
      ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hinner_ne
  calc
    Real.log
        ‖1 - (((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ =
      Real.log
        ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a) *
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))))‖ := by
      exact congrArg (fun x : ℂ => Real.log ‖x‖) hfactor
    _ =
      Real.log
        (‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ *
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) := by
      exact congrArg Real.log
        (norm_mul
          (-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a))
          (1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))))
    _ =
      Real.log ‖-(((ρ : ℂ) * Complex.exp (θ * Complex.I)) / a)‖ +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact Real.log_mul houter_norm_ne hinner_norm_ne
    _ =
      Real.log (ρ / ‖a‖) +
        Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖ := by
      exact congrArg
        (fun x : ℝ =>
          Real.log x +
            Real.log ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖)
        houter_norm


end
end LFunctions
end Boundary
