import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
# Dominated differentiation support for the log-sine integral

This file owns the pointwise exponent-derivative and endpoint-logarithm
majorant facts used by the classical log-sine integral owner.
-/

namespace LFunctions

noncomputable section

open scoped Interval

/-- The derivative value for a positive constant base at an arbitrary exponent. -/
theorem Real.sinePowerKernel_exponent_derivativeValue_at
    {a s : ℝ}
    (_ha : 0 < a) :
    (0 : ℝ) * s * a ^ (s - 1) +
        (1 : ℝ) * a ^ s * Real.log a =
      a ^ s * Real.log a := by
  have hzero_factor :
      (0 : ℝ) * s * a ^ (s - 1) = 0 := by
    calc
      (0 : ℝ) * s * a ^ (s - 1) =
          (0 : ℝ) * a ^ (s - 1) := by
        exact congrArg
          (fun x : ℝ => x * a ^ (s - 1))
          (zero_mul s)
      _ = 0 := by
        exact zero_mul (a ^ (s - 1))
  calc
    (0 : ℝ) * s * a ^ (s - 1) +
        (1 : ℝ) * a ^ s * Real.log a =
        0 + (1 : ℝ) * a ^ s * Real.log a := by
      exact congrArg
        (fun x : ℝ => x + (1 : ℝ) * a ^ s * Real.log a)
        hzero_factor
    _ = (1 : ℝ) * a ^ s * Real.log a := by
      exact zero_add ((1 : ℝ) * a ^ s * Real.log a)
    _ = a ^ s * Real.log a := by
      exact congrArg
        (fun x : ℝ => x * Real.log a)
        (one_mul (a ^ s))

/-- Pointwise derivative of the sine-power kernel with respect to the exponent
at an interior point of `[0,π]` and an arbitrary exponent. -/
theorem Real.sinePowerKernel_exponent_hasDerivAt
    (s u : ℝ)
    (hu0 : 0 < u)
    (hupi : u < Real.pi) :
    HasDerivAt
      (fun r : ℝ => (Real.sin u) ^ r)
      ((Real.sin u) ^ s * Real.log (Real.sin u))
      s := by
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hbase :
      HasDerivAt (fun _ : ℝ => Real.sin u) 0 s :=
    hasDerivAt_const s (Real.sin u)
  have hexponent :
      HasDerivAt (fun r : ℝ => r) 1 s :=
    hasDerivAt_id' s
  have hraw :
      HasDerivAt
        (fun r : ℝ => (Real.sin u) ^ r)
        ((0 : ℝ) * s * (Real.sin u) ^ (s - 1) +
          (1 : ℝ) * (Real.sin u) ^ s *
            Real.log (Real.sin u))
        s :=
    hbase.rpow hexponent hsin_pos
  exact
    hraw.congr_deriv
      (Real.sinePowerKernel_exponent_derivativeValue_at hsin_pos)

/-- A logarithm on `(0,1]` is dominated by any negative power.  This is the
scalar endpoint estimate used to dominate the exponent-derivative kernel. -/
theorem Real.abs_log_le_neg_rpow_div
    {x t : ℝ}
    (hx0 : 0 < x)
    (hx1 : x ≤ 1)
    (ht : 0 < t) :
    |Real.log x| ≤ x ^ (-t) / t := by
  have hcore :
      |Real.log x * x ^ t| < 1 / t :=
    Real.abs_log_mul_self_rpow_lt x t hx0 hx1 ht
  have hxpow_pos : 0 < x ^ t :=
    Real.rpow_pos_of_pos hx0 t
  have hxpow_abs : |x ^ t| = x ^ t :=
    abs_of_pos hxpow_pos
  have hmul :
      |Real.log x| * x ^ t < 1 / t := by
    calc
      |Real.log x| * x ^ t =
          |Real.log x| * |x ^ t| := by
        exact congrArg (fun y : ℝ => |Real.log x| * y) hxpow_abs.symm
      _ = |Real.log x * x ^ t| := by
        exact (abs_mul (Real.log x) (x ^ t)).symm
      _ < 1 / t := hcore
  have hdiv :
      |Real.log x| < (1 / t) / (x ^ t) :=
    (lt_div_iff₀' hxpow_pos).2
      (Eq.subst
        (motive := fun y : ℝ => y < 1 / t)
        (mul_comm |Real.log x| (x ^ t))
        hmul)
  have htarget :
      (1 / t) / (x ^ t) = x ^ (-t) / t := by
    have hinv_pow : (x ^ t)⁻¹ = x ^ (-t) := by
      exact (Real.rpow_neg hx0.le t).symm
    calc
      (1 / t) / (x ^ t) =
          (1 / t) * (x ^ t)⁻¹ := by
        exact div_eq_mul_inv (1 / t) (x ^ t)
      _ = (1 / t) * x ^ (-t) := by
        exact congrArg (fun y : ℝ => (1 / t) * y) hinv_pow
      _ = x ^ (-t) * (1 / t) := by
        exact mul_comm (1 / t) (x ^ (-t))
      _ = x ^ (-t) / t := by
        exact (div_eq_mul_one_div (x ^ (-t)) t).symm
  exact le_of_lt (Eq.subst (motive := fun y : ℝ => |Real.log x| < y) htarget hdiv)

/-- The pointwise exponent derivative holds almost everywhere on the interval
`Ι 0 π`; the endpoint `π` is null and the left endpoint is not in `Ioc`. -/
theorem Real.sinePowerKernel_exponent_hasDerivAt_ae_uIoc
    (ε : ℝ) :
    ∀ᵐ u ∂MeasureTheory.volume,
      u ∈ Ι (0 : ℝ) Real.pi →
        ∀ s : ℝ,
          s ∈ Metric.ball (0 : ℝ) ε →
            HasDerivAt
              (fun r : ℝ => (Real.sin u) ^ r)
              ((Real.sin u) ^ s * Real.log (Real.sin u))
              s := by
  have huIoc_eq :
      Ι (0 : ℝ) Real.pi = Set.Ioc (0 : ℝ) Real.pi :=
    Set.uIoc_of_le Real.pi_pos.le
  have hae :
      Set.Ioo (0 : ℝ) Real.pi =ᵐ[MeasureTheory.volume]
        Set.Ioc (0 : ℝ) Real.pi :=
    MeasureTheory.Ioo_ae_eq_Ioc
  exact hae.mono
    (fun u hu hmem s _hs =>
      have hmem_Ioc : u ∈ Set.Ioc (0 : ℝ) Real.pi :=
        Eq.subst
          (motive := fun t : Set ℝ => u ∈ t)
          huIoc_eq
          hmem
      have hmem_Ioo : u ∈ Set.Ioo (0 : ℝ) Real.pi :=
        hu.mpr hmem_Ioc
      Real.sinePowerKernel_exponent_hasDerivAt
        s u hmem_Ioo.1 hmem_Ioo.2)

/-- Interior sine values lie in `(0,1]`, the scalar range needed by the
endpoint logarithm estimate. -/
theorem Real.sin_mem_Ioc_zero_one_of_mem_Ioo_zero_pi
    {u : ℝ}
    (hu0 : 0 < u)
    (hupi : u < Real.pi) :
    0 < Real.sin u ∧ Real.sin u ≤ 1 := by
  exact
    ⟨Real.sin_pos_of_pos_of_lt_pi hu0 hupi, Real.sin_le_one u⟩

/-- A local exponent lower bound and the endpoint logarithm estimate dominate
the differentiated sine-power kernel at an interior point. -/
theorem Real.sinePowerKernel_logDerivative_norm_le_twoPowerMajorant
    {s ε t u : ℝ}
    (ht_pos : 0 < t)
    (hs_lower : -ε ≤ s)
    (hu0 : 0 < u)
    (hupi : u < Real.pi) :
    ‖(Real.sin u) ^ s * Real.log (Real.sin u)‖ ≤
      (Real.sin u) ^ (-ε) * ((Real.sin u) ^ (-t) / t) := by
  have hsin_range :
      0 < Real.sin u ∧ Real.sin u ≤ 1 :=
    Real.sin_mem_Ioc_zero_one_of_mem_Ioo_zero_pi hu0 hupi
  have hsin_pos : 0 < Real.sin u := hsin_range.1
  have hsin_le_one : Real.sin u ≤ 1 := hsin_range.2
  have hpow_pos : 0 < (Real.sin u) ^ s :=
    Real.rpow_pos_of_pos hsin_pos s
  have hpow_abs : |(Real.sin u) ^ s| = (Real.sin u) ^ s :=
    abs_of_pos hpow_pos
  have hpow_le :
      (Real.sin u) ^ s ≤ (Real.sin u) ^ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hsin_pos hsin_le_one hs_lower
  have hlog_le :
      |Real.log (Real.sin u)| ≤ (Real.sin u) ^ (-t) / t :=
    Real.abs_log_le_neg_rpow_div hsin_pos hsin_le_one ht_pos
  have hlog_nonneg : 0 ≤ |Real.log (Real.sin u)| :=
    abs_nonneg (Real.log (Real.sin u))
  have hpow_majorant_pos : 0 < (Real.sin u) ^ (-ε) :=
    Real.rpow_pos_of_pos hsin_pos (-ε)
  have hmul_le :
      (Real.sin u) ^ s * |Real.log (Real.sin u)| ≤
        (Real.sin u) ^ (-ε) * ((Real.sin u) ^ (-t) / t) :=
    mul_le_mul hpow_le hlog_le hlog_nonneg (le_of_lt hpow_majorant_pos)
  calc
    ‖(Real.sin u) ^ s * Real.log (Real.sin u)‖ =
        |(Real.sin u) ^ s * Real.log (Real.sin u)| := by
      exact Real.norm_eq_abs ((Real.sin u) ^ s * Real.log (Real.sin u))
    _ = |(Real.sin u) ^ s| * |Real.log (Real.sin u)| := by
      exact abs_mul ((Real.sin u) ^ s) (Real.log (Real.sin u))
    _ = (Real.sin u) ^ s * |Real.log (Real.sin u)| := by
      exact congrArg
        (fun x : ℝ => x * |Real.log (Real.sin u)|)
        hpow_abs
    _ ≤ (Real.sin u) ^ (-ε) * ((Real.sin u) ^ (-t) / t) :=
      hmul_le

/-- The fixed majorant used for differentiating the sine-power family at
exponent zero.  The exponent `-1/2` is safely above the endpoint threshold
`-1`, and the scalar `4` is the reciprocal of the quarter-radius logarithm
loss. -/
noncomputable def Real.sinePowerKernelLogDerivativeQuarterMajorant
    (u : ℝ) : ℝ :=
  (4 : ℝ) * (Real.sin u) ^ ((-1 : ℝ) / 2)

/-- The quarter radius used for the local exponent ball is positive. -/
theorem Real.one_div_four_pos :
    0 < (1 : ℝ) / 4 := by
  exact div_pos zero_lt_one zero_lt_four

/-- The reciprocal of the quarter radius is `4`. -/
theorem Real.inv_one_div_four_eq_four :
    ((1 : ℝ) / 4)⁻¹ = 4 := by
  have hmul :
      (1 : ℝ) / 4 * 4 = 1 := by
    exact div_mul_cancel₀ 1 four_ne_zero
  exact inv_eq_of_mul_eq_one_right hmul

/-- The denominator `1/4` in the endpoint logarithm estimate is nonzero. -/
theorem Real.one_div_four_ne_zero :
    (1 : ℝ) / 4 ≠ 0 :=
  (ne_of_gt Real.one_div_four_pos)

/-- The two quarter endpoint exponents add to the half endpoint exponent. -/
theorem Real.neg_one_div_four_add_neg_one_div_four :
    (-((1 : ℝ) / 4)) + (-((1 : ℝ) / 4)) = (-1 : ℝ) / 2 := by
  have hhalf_half :
      ((1 : ℝ) / 2) / 2 = (1 : ℝ) / 4 := by
    have htwo_mul_two :
        (2 : ℝ) * 2 = 4 := by
      calc
        (2 : ℝ) * 2 = 2 + 2 := by
          exact two_mul (2 : ℝ)
        _ = 4 := by
          exact two_add_two_eq_four
    calc
      ((1 : ℝ) / 2) / 2 = (1 : ℝ) / (2 * 2) := by
        exact div_div 1 2 2
      _ = (1 : ℝ) / 4 := by
        exact congrArg (fun x : ℝ => (1 : ℝ) / x) htwo_mul_two
  have htwo_quarters :
      (1 : ℝ) / 4 + (1 : ℝ) / 4 = 1 / 2 := by
    calc
      (1 : ℝ) / 4 + (1 : ℝ) / 4 =
          ((1 : ℝ) / 2) / 2 + ((1 : ℝ) / 2) / 2 := by
        exact congrArg₂ Add.add hhalf_half.symm hhalf_half.symm
      _ = (1 : ℝ) / 2 := by
        exact add_halves ((1 : ℝ) / 2)
  calc
    (-((1 : ℝ) / 4)) + (-((1 : ℝ) / 4)) =
        -((1 : ℝ) / 4 + (1 : ℝ) / 4) := by
      exact (neg_add ((1 : ℝ) / 4) ((1 : ℝ) / 4)).symm
    _ = -(1 / 2 : ℝ) := by
      exact congrArg Neg.neg htwo_quarters
    _ = (-1 : ℝ) / 2 := by
      exact (neg_div 2 1).symm

/-- Product normalization for the quarter-radius endpoint majorant. -/
theorem Real.twoPowerMajorant_quarter_eq_quarterMajorant
    {x : ℝ}
    (hx : 0 < x) :
    x ^ (-((1 : ℝ) / 4)) * (x ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4)) =
      (4 : ℝ) * x ^ ((-1 : ℝ) / 2) := by
  have hpow_mul :
      x ^ (-((1 : ℝ) / 4)) * x ^ (-((1 : ℝ) / 4)) =
        x ^ ((-1 : ℝ) / 2) := by
    calc
      x ^ (-((1 : ℝ) / 4)) * x ^ (-((1 : ℝ) / 4)) =
          x ^ ((-((1 : ℝ) / 4)) + (-((1 : ℝ) / 4))) := by
        exact (Real.rpow_add hx (-((1 : ℝ) / 4)) (-((1 : ℝ) / 4))).symm
      _ = x ^ ((-1 : ℝ) / 2) := by
        exact congrArg
          (fun e : ℝ => x ^ e)
          Real.neg_one_div_four_add_neg_one_div_four
  have hdiv :
      x ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4) =
        x ^ (-((1 : ℝ) / 4)) * 4 := by
    calc
      x ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4) =
          x ^ (-((1 : ℝ) / 4)) * (((1 : ℝ) / 4)⁻¹) := by
        exact div_eq_mul_inv (x ^ (-((1 : ℝ) / 4))) ((1 : ℝ) / 4)
      _ = x ^ (-((1 : ℝ) / 4)) * 4 := by
        exact congrArg
          (fun y : ℝ => x ^ (-((1 : ℝ) / 4)) * y)
          Real.inv_one_div_four_eq_four
  calc
    x ^ (-((1 : ℝ) / 4)) * (x ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4)) =
        x ^ (-((1 : ℝ) / 4)) *
          (x ^ (-((1 : ℝ) / 4)) * 4) := by
      exact congrArg
        (fun y : ℝ => x ^ (-((1 : ℝ) / 4)) * y)
        hdiv
    _ =
        (x ^ (-((1 : ℝ) / 4)) *
          x ^ (-((1 : ℝ) / 4))) * 4 := by
      exact (mul_assoc
        (x ^ (-((1 : ℝ) / 4)))
        (x ^ (-((1 : ℝ) / 4)))
        4).symm
    _ = x ^ ((-1 : ℝ) / 2) * 4 := by
      exact congrArg (fun y : ℝ => y * 4) hpow_mul
    _ = (4 : ℝ) * x ^ ((-1 : ℝ) / 2) := by
      exact mul_comm (x ^ ((-1 : ℝ) / 2)) 4

/-- Quarter-radius pointwise domination of the exponent-derivative kernel by
the named integrable majorant. -/
theorem Real.sinePowerKernel_logDerivative_norm_le_quarterMajorant
    {s u : ℝ}
    (hs_lower : -((1 : ℝ) / 4) ≤ s)
    (hu0 : 0 < u)
    (hupi : u < Real.pi) :
    ‖(Real.sin u) ^ s * Real.log (Real.sin u)‖ ≤
      Real.sinePowerKernelLogDerivativeQuarterMajorant u := by
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hraw :
      ‖(Real.sin u) ^ s * Real.log (Real.sin u)‖ ≤
        (Real.sin u) ^ (-((1 : ℝ) / 4)) *
          ((Real.sin u) ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4)) :=
    Real.sinePowerKernel_logDerivative_norm_le_twoPowerMajorant
      Real.one_div_four_pos
      hs_lower
      hu0
      hupi
  have hnormalize :
      (Real.sin u) ^ (-((1 : ℝ) / 4)) *
          ((Real.sin u) ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4)) =
        Real.sinePowerKernelLogDerivativeQuarterMajorant u := by
    calc
      (Real.sin u) ^ (-((1 : ℝ) / 4)) *
          ((Real.sin u) ^ (-((1 : ℝ) / 4)) / ((1 : ℝ) / 4)) =
          (4 : ℝ) * (Real.sin u) ^ ((-1 : ℝ) / 2) := by
        exact Real.twoPowerMajorant_quarter_eq_quarterMajorant hsin_pos
      _ = Real.sinePowerKernelLogDerivativeQuarterMajorant u := by
        rfl
  exact le_trans hraw (le_of_eq hnormalize)

/-- Membership in the quarter ball around zero gives the exponent lower bound
needed by the endpoint majorant. -/
theorem Real.mem_ball_zero_one_div_four_imp_neg_one_div_four_le
    {s : ℝ}
    (hs : s ∈ Metric.ball (0 : ℝ) ((1 : ℝ) / 4)) :
    -((1 : ℝ) / 4) ≤ s := by
  have hnorm :
      ‖s‖ < (1 : ℝ) / 4 :=
    mem_ball_zero_iff.mp hs
  have habs :
      |s| < (1 : ℝ) / 4 := by
    exact Eq.subst
      (motive := fun x : ℝ => x < (1 : ℝ) / 4)
      (Real.norm_eq_abs s)
      hnorm
  have hbounds :
      -((1 : ℝ) / 4) < s ∧ s < (1 : ℝ) / 4 :=
    abs_lt.mp habs
  exact le_of_lt hbounds.1

/-- Almost-everywhere quarter-radius domination on the log-sine integration
interval. -/
theorem Real.sinePowerKernel_logDerivative_norm_le_quarterMajorant_ae_uIoc :
    ∀ᵐ u ∂MeasureTheory.volume,
      u ∈ Ι (0 : ℝ) Real.pi →
        ∀ s : ℝ,
          s ∈ Metric.ball (0 : ℝ) ((1 : ℝ) / 4) →
            ‖(Real.sin u) ^ s * Real.log (Real.sin u)‖ ≤
              Real.sinePowerKernelLogDerivativeQuarterMajorant u := by
  have huIoc_eq :
      Ι (0 : ℝ) Real.pi = Set.Ioc (0 : ℝ) Real.pi :=
    Set.uIoc_of_le Real.pi_pos.le
  have hae :
      Set.Ioo (0 : ℝ) Real.pi =ᵐ[MeasureTheory.volume]
        Set.Ioc (0 : ℝ) Real.pi :=
    MeasureTheory.Ioo_ae_eq_Ioc
  exact hae.mono
    (fun u hu hmem s hs =>
      have hmem_Ioc : u ∈ Set.Ioc (0 : ℝ) Real.pi :=
        Eq.subst
          (motive := fun t : Set ℝ => u ∈ t)
          huIoc_eq
          hmem
      have hmem_Ioo : u ∈ Set.Ioo (0 : ℝ) Real.pi :=
        hu.mpr hmem_Ioc
      have hs_lower :
          -((1 : ℝ) / 4) ≤ s :=
        Real.mem_ball_zero_one_div_four_imp_neg_one_div_four_le hs
      Real.sinePowerKernel_logDerivative_norm_le_quarterMajorant
        hs_lower hmem_Ioo.1 hmem_Ioo.2)

/-- The exponent `-1/2` lies in the integrable sine-power range. -/
theorem Real.neg_one_lt_neg_one_div_two :
    (-1 : ℝ) < (-1 : ℝ) / 2 := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hneg : -1 < -(1 / 2 : ℝ) :=
    neg_lt_neg hhalf_lt_one
  have hneg_half : -(1 / 2 : ℝ) = (-1 : ℝ) / 2 := by
    exact (neg_div 2 1).symm
  exact
    Eq.subst
      (motive := fun x : ℝ => -1 < x)
      hneg_half
      hneg

end

end LFunctions
