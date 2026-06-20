import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroFreePrimitive.SingleFactorAlgebra.Owner

/-!
# Zero-free primitive and Jensen boundary average

This owner layer was split from `ZeroFreePrimitive.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The affine disk factor `z ↦ 1 - c z` is entire. -/
theorem complex_one_sub_mul_id_analyticAt
    (c z : ℂ) :
    AnalyticAt ℂ (fun w : ℂ => 1 - c * w) z := by
  exact analyticAt_const.sub (analyticAt_const.mul analyticAt_id)

/-- The affine disk factor `1 - c z` has no zeros on the closed unit disk when
`c` is contracting. -/
theorem complex_one_sub_mul_id_ne_zero_on_closed_unitDisk
    {c z : ℂ}
    (hc : ‖c‖ < 1)
    (hz : ‖z‖ ≤ 1) :
    1 - c * z ≠ 0 := by
  intro hzero
  have hmul_eq_one : c * z = 1 :=
    (sub_eq_zero.mp hzero).symm
  have hnorm_mul_eq_one : ‖c * z‖ = 1 :=
    Eq.trans (congrArg norm hmul_eq_one) norm_one
  have hnorm_mul_le : ‖c * z‖ ≤ ‖c‖ := by
    have hmul_norm : ‖c * z‖ = ‖c‖ * ‖z‖ :=
      norm_mul c z
    have hc_nonneg : 0 ≤ ‖c‖ :=
      norm_nonneg c
    have hmul_le : ‖c‖ * ‖z‖ ≤ ‖c‖ * 1 :=
      mul_le_mul_of_nonneg_left hz hc_nonneg
    have hmul_one : ‖c‖ * 1 = ‖c‖ :=
      mul_one ‖c‖
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hmul_norm.symm
      (le_trans hmul_le (le_of_eq hmul_one))
  have hone_le_c : 1 ≤ ‖c‖ :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ ‖c‖)
      hnorm_mul_eq_one
      hnorm_mul_le
  exact (not_le_of_gt hc) hone_le_c

/-- Contractivity is preserved by complex conjugation. -/
theorem complex_norm_conj_lt_one
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    ‖(starRingEnd ℂ) q‖ < 1 := by
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    (RCLike.norm_conj q).symm
    hq

/-- The negative-orientation boundary factor has the same norm as the
positive-orientation factor with conjugated coefficient. -/
theorem complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
    (q : ℂ)
    (θ : ℝ) :
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
      ‖1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I)‖ := by
  have hconj_exp :
      (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) =
        Complex.exp (θ * Complex.I) := by
    calc
      (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) =
          Complex.exp ((starRingEnd ℂ) (-(θ * Complex.I))) := by
        exact (Complex.exp_conj (-(θ * Complex.I))).symm
      _ = Complex.exp (θ * Complex.I) := by
        have harg :
            (starRingEnd ℂ) (-(θ * Complex.I)) = θ * Complex.I := by
          calc
            (starRingEnd ℂ) (-(θ * Complex.I)) =
                -((starRingEnd ℂ) (θ * Complex.I)) := by
              exact map_neg (starRingEnd ℂ) (θ * Complex.I)
            _ = -(((starRingEnd ℂ) (θ : ℂ)) *
                ((starRingEnd ℂ) Complex.I)) := by
              exact congrArg Neg.neg
                (map_mul (starRingEnd ℂ) (θ : ℂ) Complex.I)
            _ = -((θ : ℂ) * (-Complex.I)) := by
              have htheta :
                  (starRingEnd ℂ) (θ : ℂ) = (θ : ℂ) :=
                Complex.conj_ofReal θ
              have hI :
                  (starRingEnd ℂ) Complex.I = -Complex.I :=
                Complex.conj_I
              exact Eq.trans
                (congrArg
                  (fun z : ℂ =>
                    -(z * ((starRingEnd ℂ) Complex.I)))
                  htheta)
                (congrArg (fun z : ℂ => -((θ : ℂ) * z)) hI)
            _ = (θ : ℂ) * Complex.I := by
              exact Eq.trans
                (neg_mul_eq_mul_neg (θ : ℂ) (-Complex.I))
                (congrArg
                  (fun z : ℂ => (θ : ℂ) * z)
                  (neg_neg Complex.I))
        exact congrArg Complex.exp harg
  have hconj_factor :
      (starRingEnd ℂ) (1 - q * Complex.exp (-(θ * Complex.I))) =
        1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I) := by
    calc
      (starRingEnd ℂ) (1 - q * Complex.exp (-(θ * Complex.I))) =
          (starRingEnd ℂ) 1 -
            (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))) := by
        exact map_sub (starRingEnd ℂ) 1
          (q * Complex.exp (-(θ * Complex.I)))
      _ = 1 -
            (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))) := by
        exact congrArg
          (fun x : ℂ =>
            x - (starRingEnd ℂ) (q * Complex.exp (-(θ * Complex.I))))
          (map_one (starRingEnd ℂ))
      _ =
          1 - (starRingEnd ℂ) q *
            (starRingEnd ℂ) (Complex.exp (-(θ * Complex.I))) := by
        exact congrArg (fun x : ℂ => 1 - x)
          (map_mul (starRingEnd ℂ) q (Complex.exp (-(θ * Complex.I))))
      _ = 1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I) := by
        exact congrArg (fun x : ℂ => 1 - (starRingEnd ℂ) q * x) hconj_exp
  calc
    ‖1 - q * Complex.exp (-(θ * Complex.I))‖ =
        ‖(starRingEnd ℂ)
          (1 - q * Complex.exp (-(θ * Complex.I)))‖ := by
      exact (RCLike.norm_conj
        (1 - q * Complex.exp (-(θ * Complex.I)))).symm
    _ = ‖1 - (starRingEnd ℂ) q * Complex.exp (θ * Complex.I)‖ := by
      exact congrArg norm hconj_factor

/-- The center value of the affine disk factor has zero logarithmic norm. -/
theorem complex_one_sub_mul_id_center_log_norm_eq_zero
    (c : ℂ) :
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ = 0 := by
  have hmul_zero : c * (0 : ℂ) = 0 :=
    mul_zero c
  have hvalue : (fun z : ℂ => 1 - c * z) 0 = 1 := by
    calc
      (fun z : ℂ => 1 - c * z) 0 = 1 - c * 0 := rfl
      _ = 1 - 0 := by
        exact congrArg (fun x : ℂ => 1 - x) hmul_zero
      _ = 1 := by
        exact sub_zero 1
  have hnorm : ‖(fun z : ℂ => 1 - c * z) 0‖ = 1 := by
    calc
      ‖(fun z : ℂ => 1 - c * z) 0‖ = ‖(1 : ℂ)‖ := by
        exact congrArg norm hvalue
      _ = 1 :=
        norm_one
  calc
    Real.log ‖(fun z : ℂ => 1 - c * z) 0‖ =
        Real.log 1 := by
      exact congrArg Real.log hnorm
    _ = 0 :=
      Real.log_one

/-- Analytic-log mean theorem for the positive Fourier orientation of the
contracting affine disk factor. -/
theorem complex_log_one_sub_contracting_positive_fourier_mean_zero
    {c : ℂ}
    (hc : ‖c‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
        0 := by
    let G : ℂ → ℂ := fun z => 1 - c * z
    have hG : ∀ z : ℂ, AnalyticAt ℂ G z := by
      intro z
      exact complex_one_sub_mul_id_analyticAt c z
    have hzero :
        ∀ z : ℂ, ‖z‖ ≤ (1 : ℝ) → G z ≠ 0 := by
      intro z hz
      exact complex_one_sub_mul_id_ne_zero_on_closed_unitDisk hc hz
    exact
      match entireFunction_zeroFreeOnClosedDisk_exists_analyticLog
          G hG (le_refl (1 : ℝ)) hzero with
      | Exists.intro L hL_data =>
          match hL_data with
          | And.intro hL_an hL_tail =>
              match hL_tail with
              | And.intro hL_log hL_center =>
                  have hmean :
                      (2 * Real.pi)⁻¹ *
                          (∫ θ in (0 : ℝ)..(2 * Real.pi),
                            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re) =
                        (L 0).re :=
                    entireFunction_analyticLog_re_holomorphicMeanValue_circle
                      L (le_refl (1 : ℝ)) hL_an
                  have hboundary :
                      (∫ θ in (0 : ℝ)..(2 * Real.pi),
                          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖) =
                        ∫ θ in (0 : ℝ)..(2 * Real.pi),
                          (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re := by
                    exact intervalIntegral.integral_congr fun θ _hθ =>
                      by
                        have hpoint :
                            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ ≤
                              (1 : ℝ) := by
                          calc
                            ‖(((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ =
                                ‖((1 : ℝ) : ℂ)‖ * ‖Complex.exp (θ * Complex.I)‖ := by
                              exact norm_mul (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I))
                            _ = 1 * ‖Complex.exp (θ * Complex.I)‖ := by
                              exact congrArg
                                (fun x : ℝ => x * ‖Complex.exp (θ * Complex.I)‖)
                                norm_one
                            _ = 1 * 1 := by
                              exact congrArg (fun x : ℝ => 1 * x)
                                (Complex.norm_exp_ofReal_mul_I θ)
                            _ = 1 := by
                              exact one_mul 1
                            _ ≤ (1 : ℝ) := by
                              exact le_refl 1
                        have hlog_re :
                            (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re =
                              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ :=
                          entireFunction_analyticLogBranch_re_eq_log_norm
                            G L hpoint hL_log
                        have hG_eval :
                            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
                              1 - c * Complex.exp (θ * Complex.I) := by
                          calc
                            G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) =
                                1 - c * (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) := rfl
                            _ = 1 - (c * (((1 : ℝ) : ℂ)) * Complex.exp (θ * Complex.I)) := by
                              exact congrArg (fun x : ℂ => 1 - x)
                                (mul_assoc c (((1 : ℝ) : ℂ)) (Complex.exp (θ * Complex.I))).symm
                            _ = 1 - (c * 1 * Complex.exp (θ * Complex.I)) := by
                              exact congrArg
                                (fun x : ℂ => 1 - (c * x * Complex.exp (θ * Complex.I)))
                                rfl
                            _ = 1 - c * Complex.exp (θ * Complex.I) := by
                              exact congrArg (fun x : ℂ => 1 - x)
                                (congrArg (fun x : ℂ => x * Complex.exp (θ * Complex.I))
                                  (mul_one c))
                        calc
                          Real.log ‖1 - c * Complex.exp (θ * Complex.I)‖ =
                              Real.log ‖G (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))‖ := by
                            exact congrArg (fun x : ℂ => Real.log ‖x‖) hG_eval.symm
                          _ = (L (((1 : ℝ) : ℂ) * Complex.exp (θ * Complex.I))).re :=
                            hlog_re.symm
                  have hcenter_zero :
                      (L 0).re = 0 := by
                    exact Eq.trans hL_center (complex_one_sub_mul_id_center_log_norm_eq_zero c)
                  Eq.trans
                    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
                    (Eq.trans hmean hcenter_zero)

/-- The Fourier-mode logarithmic mean for a contracting inner disk factor.

For `‖q‖ < 1`, the branch
`log (1 - q * exp (-θ I)) = -∑ n≥1 q^n exp (-n θ I) / n` is uniformly
convergent on the Jensen circle.  Every nonzero Fourier mode has zero angular
mean, hence the real logarithmic norm has zero normalized mean.  Cf.
Titchmarsh, *The Theory of Functions*, §5. -/
theorem complex_log_one_sub_contracting_fourier_mean_zero
    {q : ℂ}
    (hq : ‖q‖ < 1) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
      0 := by
  have hconj_contract : ‖(starRingEnd ℂ) q‖ < 1 :=
    complex_norm_conj_lt_one hq
  have hpositive :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - (starRingEnd ℂ) q *
              Complex.exp (θ * Complex.I)‖) =
        0 :=
    complex_log_one_sub_contracting_positive_fourier_mean_zero hconj_contract
  have hboundary :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - q * Complex.exp (-(θ * Complex.I))‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - (starRingEnd ℂ) q *
            Complex.exp (θ * Complex.I)‖ := by
    exact intervalIntegral.integral_congr fun θ _hθ =>
      congrArg Real.log
        (complex_one_sub_contracting_negativeMode_norm_eq_conj_positiveMode_norm
          q θ)
  exact Eq.trans
    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hboundary)
    hpositive

/-- The normalized zero location `a / ρ` is strictly inside the unit disk. -/
theorem entireFunction_singleZeroFactor_normalized_zero_norm_lt_one
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    ‖a / (ρ : ℂ)‖ < 1 := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hnorm_div :
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ρ := by
    calc
      ‖a / (ρ : ℂ)‖ = ‖a‖ / ‖(ρ : ℂ)‖ := by
        exact norm_div a (ρ : ℂ)
      _ = ‖a‖ / |ρ| := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (Complex.norm_real ρ)
      _ = ‖a‖ / ρ := by
        exact congrArg (fun x : ℝ => ‖a‖ / x) (abs_of_pos hρ_pos)
  have hratio_lt : ‖a‖ / ρ < 1 :=
    (div_lt_one hρ_pos).mpr haρ
  exact Eq.subst
    (motive := fun x : ℝ => x < 1)
    hnorm_div.symm
    hratio_lt

/-- Algebraic transport from the Jensen inner factor to the normalized
contracting Fourier factor. -/
theorem entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ)
    (θ : ℝ) :
    1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I))) =
      1 - (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
  have hρ_pos : 0 < ρ :=
    lt_of_le_of_lt (norm_nonneg a) haρ
  have hdiv :
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
        (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
    calc
      a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)) =
          a * (((ρ : ℂ) * Complex.exp (θ * Complex.I))⁻¹) := by
        exact div_eq_mul_inv a ((ρ : ℂ) * Complex.exp (θ * Complex.I))
      _ = a * ((Complex.exp (θ * Complex.I))⁻¹ * (ρ : ℂ)⁻¹) := by
        exact congrArg (fun x : ℂ => a * x)
          (mul_inv_rev (ρ : ℂ) (Complex.exp (θ * Complex.I)))
      _ = a * ((ρ : ℂ)⁻¹ * (Complex.exp (θ * Complex.I))⁻¹) := by
        exact congrArg (fun x : ℂ => a * x)
          (mul_comm (Complex.exp (θ * Complex.I))⁻¹ (ρ : ℂ)⁻¹)
      _ = (a * (ρ : ℂ)⁻¹) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact (mul_assoc a (ρ : ℂ)⁻¹ (Complex.exp (θ * Complex.I))⁻¹).symm
      _ = (a / (ρ : ℂ)) * (Complex.exp (θ * Complex.I))⁻¹ := by
        exact congrArg
          (fun x : ℂ => x * (Complex.exp (θ * Complex.I))⁻¹)
          (div_eq_mul_inv a (ρ : ℂ)).symm
      _ = (a / (ρ : ℂ)) * Complex.exp (-(θ * Complex.I)) := by
        exact congrArg (fun x : ℂ => (a / (ρ : ℂ)) * x)
          (Complex.exp_neg (θ * Complex.I)).symm
  exact congrArg (fun x : ℂ => 1 - x) hdiv

/-- The logarithmic power-series mean for an inside-disk linear factor
vanishes on the Jensen boundary. -/
theorem entireFunction_singleZeroFactor_inner_log_mean_zero_from_powerSeries
    {a : ℂ}
    {ρ : ℝ}
    (haρ : ‖a‖ < ρ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log
            ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      0 := by
  have hq : ‖a / (ρ : ℂ)‖ < 1 :=
    entireFunction_singleZeroFactor_normalized_zero_norm_lt_one haρ
  have hmean :
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - (a / (ρ : ℂ)) *
              Complex.exp (-(θ * Complex.I))‖) =
        0 :=
    complex_log_one_sub_contracting_fourier_mean_zero hq
  have hintegrand :
      (fun θ : ℝ =>
        Real.log
          ‖1 - (a / ((ρ : ℂ) * Complex.exp (θ * Complex.I)))‖) =
      (fun θ : ℝ =>
        Real.log ‖1 - (a / (ρ : ℂ)) *
          Complex.exp (-(θ * Complex.I))‖) := by
    funext θ
    exact congrArg (fun z : ℂ => Real.log ‖z‖)
      (entireFunction_singleZeroFactor_inner_eq_contracting_fourier_factor
        haρ θ)
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      (2 * Real.pi)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * Real.pi), f θ) =
        0)
    hintegrand.symm
    hmean


end
end LFunctions
end Boundary
