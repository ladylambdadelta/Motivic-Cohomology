import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# The classical log-sine integral

This file owns the classical analysis package behind
`∫₀^π log (sin u) du = -π log 2`.

The intended proof chain is:

* split the sine-power integral into two half-intervals;
* use the Euler-Beta substitution on `[0, π/2]`;
* compare the Euler-Beta integral with Gamma quotients;
* differentiate at exponent `0`;
* use Legendre duplication in logarithmic-derivative form.
-/

namespace LFunctions

noncomputable section

/-- The sine-power integral on `[0,π]`. -/
noncomputable def Real.sinePowerIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.pi, (Real.sin u) ^ s

/-- The half-interval sine-power integral on `[0,π/2]`. -/
noncomputable def Real.sinePowerHalfIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin u) ^ s

/-- The real Euler-Beta integral associated to the sine-power exponent. -/
noncomputable def Real.sinePowerEulerBetaIntegral
    (s : ℝ) : ℝ :=
  (Complex.betaIntegral (((s + 1) / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)).re

/-- The real unit-interval Beta integral obtained after `t = sin² u`. -/
noncomputable def Real.sinePowerEulerBetaRealIntegral
    (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    t ^ (((s + 1) / 2) - 1) * (1 - t) ^ ((1 / 2 : ℝ) - 1)

/-- The Gamma-ratio associated to the sine-power integral. -/
noncomputable def Real.sinePowerGammaRatio
    (s : ℝ) : ℝ :=
  Real.sqrt Real.pi *
    Real.Gamma ((s + 1) / 2) /
      Real.Gamma (s / 2 + 1)

/-- Real logarithmic derivative of Gamma on its regular locus. -/
noncomputable def Real.gammaLogDeriv
    (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

/-- Elementary scalar cancellation for the half-interval normalization. -/
theorem Real.two_mul_one_half_mul
    (x : ℝ) :
    2 * ((1 / 2 : ℝ) * x) = x := by
  have htwo_half : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by
    calc
      (2 : ℝ) * (1 / 2 : ℝ) = (2 : ℝ) * (2 : ℝ)⁻¹ := by
        exact congrArg (fun y : ℝ => (2 : ℝ) * y) (one_div (2 : ℝ))
      _ = 1 := by
        exact mul_inv_cancel₀ (2 : ℝ) two_ne_zero
  calc
    2 * ((1 / 2 : ℝ) * x) = (2 * (1 / 2 : ℝ)) * x := by
      exact (mul_assoc (2 : ℝ) (1 / 2 : ℝ) x).symm
    _ = 1 * x := by
      exact congrArg (fun y : ℝ => y * x) htwo_half
    _ = x := by
      exact one_mul x

/-- Strict lower bound for the left Euler-Beta parameter in the sine-power integral. -/
theorem Real.sinePowerEulerBeta_leftParameter_pos
    {s : ℝ}
    (hs : -1 < s) :
    0 < (s + 1) / 2 := by
  have hshift : (-1 : ℝ) + 1 < s + 1 :=
    add_lt_add_right hs 1
  have hsum : 0 < s + 1 := by
    have hzero : (-1 : ℝ) + 1 = 0 :=
      neg_add_cancel 1
    exact
      Eq.subst
        (motive := fun x : ℝ => x < s + 1)
        hzero
        hshift
  exact div_pos hsum zero_lt_two

/-- Positivity of the left Euler-Beta parameter is equivalent to the endpoint
integrability exponent bound needed at `0`. -/
theorem Real.sinePowerExponent_gt_neg_one_of_leftParameter_pos
    {s : ℝ}
    (hleft : 0 < (s + 1) / 2) :
    -1 < s := by
  have htwo : (0 : ℝ) < 2 :=
    zero_lt_two
  have hmul :
      0 * (2 : ℝ) < ((s + 1) / 2) * 2 :=
    mul_lt_mul_of_pos_right hleft htwo
  have hsum : 0 < s + 1 := by
    calc
      0 = 0 * (2 : ℝ) := by
        exact (zero_mul 2).symm
      _ < ((s + 1) / 2) * 2 := hmul
      _ = s + 1 := by
        exact div_mul_cancel₀ (s + 1) two_ne_zero
  have hshift : 0 - 1 < (s + 1) - 1 :=
    sub_lt_sub_right hsum 1
  calc
    -1 = 0 - 1 := by
      exact (zero_sub 1).symm
    _ < (s + 1) - 1 := hshift
    _ = s := by
      exact add_sub_cancel s 1

/-- Strict lower bound for the right Euler-Beta parameter in the sine-power integral. -/
theorem Real.sinePowerEulerBeta_rightParameter_pos :
    0 < (1 / 2 : ℝ) :=
  one_half_pos

/-- Real Gamma is nonzero on the positive real axis. -/
theorem Real.Gamma_ne_zero_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    Real.Gamma x ≠ 0 :=
  (Real.Gamma_pos_of_pos hx).ne'

/-- The denominator parameter in the sine-power Beta/Gamma formula. -/
theorem Real.sinePowerEulerBeta_parameter_sum
    (s : ℝ) :
    (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1 := by
  calc
    (s + 1) / 2 + (1 / 2 : ℝ) =
        (s + 1 + 1) / 2 := by
      exact (add_div (s + 1) 1 2).symm
    _ = (s + 2) / 2 := by
      exact congrArg (fun x : ℝ => x / 2) (add_assoc s 1 1)
    _ = s / 2 + 2 / 2 := by
      exact add_div s 2 2
    _ = s / 2 + 1 := by
      exact congrArg (fun x : ℝ => s / 2 + x) (div_self two_ne_zero)

/-- Positivity of the Gamma-ratio denominator parameter. -/
theorem Real.sinePowerGammaRatio_denominatorParameter_pos
    {s : ℝ}
    (hs : -1 < s) :
    0 < s / 2 + 1 := by
  have hleft : 0 < (s + 1) / 2 :=
    Real.sinePowerEulerBeta_leftParameter_pos hs
  have hright : 0 < (1 / 2 : ℝ) :=
    Real.sinePowerEulerBeta_rightParameter_pos
  have hsum :
      (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1 :=
    Real.sinePowerEulerBeta_parameter_sum s
  exact Eq.subst
    (motive := fun x : ℝ => 0 < x)
    hsum
    (add_pos hleft hright)

/-- Positivity of the Gamma-ratio denominator at exponent `0`. -/
theorem Real.sinePowerGammaRatio_denominatorParameter_zero_pos :
    0 < (0 : ℝ) / 2 + 1 := by
  have hzero_gt : -1 < (0 : ℝ) :=
    neg_lt_zero.mpr one_pos
  exact Real.sinePowerGammaRatio_denominatorParameter_pos hzero_gt

/-- Endpoint normalization for reflecting `[0, π/2]` across `π/2`. -/
theorem Real.pi_sub_half :
    Real.pi - Real.pi / 2 = Real.pi / 2 := by
  have hhalf : Real.pi / 2 + Real.pi / 2 = Real.pi :=
    add_halves Real.pi
  calc
    Real.pi - Real.pi / 2 =
        (Real.pi / 2 + Real.pi / 2) - Real.pi / 2 := by
      exact congrArg (fun x : ℝ => x - Real.pi / 2) hhalf.symm
    _ = Real.pi / 2 := by
      exact add_sub_cancel (Real.pi / 2) (Real.pi / 2)

/-- Right endpoint normalization for reflecting by `u ↦ π-u`. -/
theorem Real.pi_sub_zero :
    Real.pi - 0 = Real.pi :=
  sub_zero Real.pi

/-- Integrability of the model endpoint singularity `u^s` near `0`. -/
theorem Real.sinePowerEndpointModel_intervalIntegrable_zero_half
    (s : ℝ)
    (hs : -1 < s) :
    IntervalIntegrable
      (fun u : ℝ => u ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  exact intervalIntegral.intervalIntegrable_rpow' hs

/-- Nonnegative sine powers are continuous, hence interval-integrable on the
left half interval. -/
theorem Real.sinePowerKernel_intervalIntegrable_zero_half_of_nonneg
    (s : ℝ)
    (hs_nonneg : 0 ≤ s) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  have hcontinuous :
      Continuous (fun u : ℝ => (Real.sin u) ^ s) :=
    Real.continuous_sin.rpow_const
      (fun _ => Or.inr hs_nonneg)
  exact hcontinuous.intervalIntegrable (0 : ℝ) (Real.pi / 2)

/-- Pointwise domination of negative sine powers by the endpoint model on
`(0,π/2]`, with the explicit Jordan constant. -/
theorem Real.sinePowerKernel_neg_le_endpointModel_const
    (s u : ℝ)
    (hs_neg : s < 0)
    (hu0 : 0 < u)
    (huhalf : u ≤ Real.pi / 2) :
    (Real.sin u) ^ s ≤
      (2 / Real.pi : ℝ) ^ s * u ^ s := by
  have hc_pos : 0 < (2 / Real.pi : ℝ) :=
    div_pos zero_lt_two Real.pi_pos
  have hc_nonneg : 0 ≤ (2 / Real.pi : ℝ) :=
    le_of_lt hc_pos
  have hu_nonneg : 0 ≤ u :=
    le_of_lt hu0
  have hcu_pos : 0 < (2 / Real.pi : ℝ) * u :=
    mul_pos hc_pos hu0
  have hsin_lower : (2 / Real.pi : ℝ) * u ≤ Real.sin u :=
    Real.mul_le_sin hu_nonneg huhalf
  have hpow :
      (Real.sin u) ^ s ≤ ((2 / Real.pi : ℝ) * u) ^ s :=
    Real.rpow_le_rpow_of_nonpos hcu_pos hsin_lower (le_of_lt hs_neg)
  calc
    (Real.sin u) ^ s ≤ ((2 / Real.pi : ℝ) * u) ^ s := hpow
    _ = (2 / Real.pi : ℝ) ^ s * u ^ s := by
      exact Real.mul_rpow hc_nonneg hu_nonneg

/-- Negative sine powers on `[0,π/2]` are dominated by the endpoint model via
Jordan's lower bound `2/π * u ≤ sin u`. -/
theorem Real.sinePowerKernel_intervalIntegrable_zero_half_of_neg_from_endpointModel
    (s : ℝ)
    (hs : -1 < s)
    (hs_neg : s < 0)
    (hmodel :
      IntervalIntegrable
        (fun u : ℝ => u ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2)) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 :=
    le_of_lt Real.pi_div_two_pos
  rw [intervalIntegral.intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  have hmodel_const :
      IntervalIntegrable
        (fun u : ℝ => (2 / Real.pi : ℝ) ^ s * u ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2) :=
    hmodel.const_mul ((2 / Real.pi : ℝ) ^ s)
  rw [intervalIntegral.intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at hmodel_const
  have hcontinuousOn :
      ContinuousOn
        (fun u : ℝ => (Real.sin u) ^ s)
        (Set.Ioc (0 : ℝ) (Real.pi / 2)) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hupi : u < Real.pi :=
      lt_of_le_of_lt hu.2 (half_lt_self Real.pi_pos)
    have hsin_ne : Real.sin u ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi hu0 hupi).ne'
    exact
      (Real.continuous_sin.continuousAt.rpow_const
        (Or.inl hsin_ne)).continuousWithinAt
  exact
    Integrable.mono' hmodel_const
      (hcontinuousOn.aestronglyMeasurable measurableSet_Ioc)
      (by
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc] with u hu
        have hdom :
            (Real.sin u) ^ s ≤
              (2 / Real.pi : ℝ) ^ s * u ^ s :=
          Real.sinePowerKernel_neg_le_endpointModel_const
            s u hs_neg hu.1 hu.2
        have hnonneg : 0 ≤ (Real.sin u) ^ s :=
          Real.rpow_nonneg
            (Real.sin_nonneg_of_nonneg_of_le_pi
              (le_of_lt hu.1)
              (le_trans hu.2 (half_le_self Real.pi_pos.le)))
            s
        exact
          (Real.norm_of_nonneg hnonneg).trans_le hdom)

/-- Local comparison of `sin u ^ s` with the model endpoint singularity near
`0`, in the integrability form needed for the left half-interval. -/
theorem Real.sinePowerKernel_intervalIntegrable_zero_half_from_endpointModel
    (s : ℝ)
    (hs : -1 < s)
    (hmodel :
      IntervalIntegrable
        (fun u : ℝ => u ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2)) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  by_cases hs_nonneg : 0 ≤ s
  · exact
      Real.sinePowerKernel_intervalIntegrable_zero_half_of_nonneg
        s hs_nonneg
  · have hs_neg : s < 0 :=
      lt_of_not_ge hs_nonneg
    exact
      Real.sinePowerKernel_intervalIntegrable_zero_half_of_neg_from_endpointModel
        s hs hs_neg hmodel

/-- Endpoint integrability of the sine-power kernel on `[0,π/2]`. -/
theorem Real.sinePowerKernel_intervalIntegrable_zero_half
    (s : ℝ)
    (hs : -1 < s) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  exact
    Real.sinePowerKernel_intervalIntegrable_zero_half_from_endpointModel
      s hs
      (Real.sinePowerEndpointModel_intervalIntegrable_zero_half s hs)

/-- Reflection transports left endpoint integrability to the right endpoint
near `π`. -/
theorem Real.sinePowerKernel_intervalIntegrable_half_pi_from_reflection
    (s : ℝ)
    (hs : -1 < s)
    (hleft :
      IntervalIntegrable
        (fun u : ℝ => (Real.sin u) ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2)) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (Real.pi / 2)
      Real.pi := by
  have hreflected :
      IntervalIntegrable
        (fun u : ℝ => (Real.sin (Real.pi - u)) ^ s)
        MeasureTheory.volume
        (Real.pi / 2)
        Real.pi := by
    have hraw :
        IntervalIntegrable
          (fun u : ℝ => (Real.sin (Real.pi - u)) ^ s)
          MeasureTheory.volume
          Real.pi
          (Real.pi / 2) := by
      simpa [Real.pi_sub_zero, Real.pi_sub_half] using
        (IntervalIntegrable.comp_sub_left hleft Real.pi)
    exact hraw.symm
  exact
    hreflected.congr
      (Filter.Eventually.of_forall
        (fun u => by
          exact congrArg (fun x : ℝ => x ^ s) (Real.sin_pi_sub u)))

/-- Endpoint integrability of the sine-power kernel on `[π/2,π]`. -/
theorem Real.sinePowerKernel_intervalIntegrable_half_pi
    (s : ℝ)
    (hs : -1 < s) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (Real.pi / 2)
      Real.pi := by
  exact
    Real.sinePowerKernel_intervalIntegrable_half_pi_from_reflection
      s hs
      (Real.sinePowerKernel_intervalIntegrable_zero_half s hs)

/-- Adjacent-interval additivity for the sine-power kernel at `π/2`. -/
theorem Real.sinePowerIntegral_split_at_half_from_intervalIntegrable
    (s : ℝ)
    (hleft :
      IntervalIntegrable
        (fun u : ℝ => (Real.sin u) ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2))
    (hright :
      IntervalIntegrable
        (fun u : ℝ => (Real.sin u) ^ s)
        MeasureTheory.volume
        (Real.pi / 2)
        Real.pi) :
    Real.sinePowerIntegral s =
      Real.sinePowerHalfIntegral s +
        ∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s := by
  unfold Real.sinePowerIntegral Real.sinePowerHalfIntegral
  exact
    (intervalIntegral.integral_add_adjacent_intervals
      hleft
      hright).symm

/-- Interval additivity for the sine-power integral at `π/2`. -/
theorem Real.sinePowerIntegral_split_at_half
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      Real.sinePowerHalfIntegral s +
        ∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s := by
  exact
    Real.sinePowerIntegral_split_at_half_from_intervalIntegrable
      s
      (Real.sinePowerKernel_intervalIntegrable_zero_half s hs)
      (Real.sinePowerKernel_intervalIntegrable_half_pi s hs)

/-- Pointwise reflection of the sine-power kernel across `π/2`. -/
theorem Real.sinePowerKernel_reflection_pointwise
    (s u : ℝ) :
    (Real.sin (Real.pi - u)) ^ s = (Real.sin u) ^ s := by
  exact congrArg (fun x : ℝ => x ^ s) (Real.sin_pi_sub u)

/-- Affine reflection changes the upper half-interval to the lower half-interval. -/
theorem Real.sinePowerIntegral_upperHalf_reflection_changeOfVariables
    (s : ℝ)
    (hs : -1 < s) :
    (∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s) =
      ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin (Real.pi - u)) ^ s := by
  let f : ℝ → ℝ := fun u : ℝ => (Real.sin u) ^ s
  have hchange :
      (∫ u in (0 : ℝ)..(Real.pi / 2), f (Real.pi - u)) =
        ∫ u in (Real.pi - Real.pi / 2)..(Real.pi - 0), f u :=
    intervalIntegral.integral_comp_sub_left
      (f := f)
      (a := (0 : ℝ))
      (b := Real.pi / 2)
      Real.pi
  calc
    (∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s) =
        ∫ u in (Real.pi - Real.pi / 2)..Real.pi, f u := by
      exact congrArg
        (fun a : ℝ => ∫ u in a..Real.pi, f u)
        Real.pi_sub_half.symm
    _ = ∫ u in (Real.pi - Real.pi / 2)..(Real.pi - 0), f u := by
      exact congrArg
        (fun b : ℝ => ∫ u in (Real.pi - Real.pi / 2)..b, f u)
        Real.pi_sub_zero.symm
    _ = ∫ u in (0 : ℝ)..(Real.pi / 2), f (Real.pi - u) := by
      exact hchange.symm
    _ = ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin (Real.pi - u)) ^ s := by
      rfl

/-- The reflected lower-half integrand has the same interval integral as the
ordinary lower-half sine-power integrand. -/
theorem Real.sinePowerIntegral_reflectedLowerHalf_eq_half
    (s : ℝ) :
    (∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin (Real.pi - u)) ^ s) =
      Real.sinePowerHalfIntegral s := by
  unfold Real.sinePowerHalfIntegral
  exact
    intervalIntegral.integral_congr
      (fun u _hu => Real.sinePowerKernel_reflection_pointwise s u)

/-- Reflection of the upper half-interval by `u ↦ π - u`. -/
theorem Real.sinePowerIntegral_reflected_upperHalf_eq_half
    (s : ℝ)
    (hs : -1 < s) :
    (∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s) =
      Real.sinePowerHalfIntegral s := by
  exact
    Eq.trans
      (Real.sinePowerIntegral_upperHalf_reflection_changeOfVariables s hs)
      (Real.sinePowerIntegral_reflectedLowerHalf_eq_half s)

/-- Algebra converting the split/reflected sine-power integral into twice the
half-interval integral. -/
theorem Real.sinePowerIntegral_eq_two_mul_halfIntegral_of_split_reflection
    (s : ℝ)
    (hsplit :
      Real.sinePowerIntegral s =
        Real.sinePowerHalfIntegral s +
          ∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s)
    (hreflect :
      (∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s) =
        Real.sinePowerHalfIntegral s) :
    Real.sinePowerIntegral s =
      2 * Real.sinePowerHalfIntegral s := by
  calc
    Real.sinePowerIntegral s =
        Real.sinePowerHalfIntegral s +
          ∫ u in (Real.pi / 2)..Real.pi, (Real.sin u) ^ s := hsplit
    _ = Real.sinePowerHalfIntegral s + Real.sinePowerHalfIntegral s := by
      exact congrArg (fun x : ℝ => Real.sinePowerHalfIntegral s + x) hreflect
    _ = 2 * Real.sinePowerHalfIntegral s := by
      exact (two_mul (Real.sinePowerHalfIntegral s)).symm

/-- Reflection symmetry splits the sine-power integral into twice the
half-interval integral. -/
theorem Real.sinePowerIntegral_eq_two_mul_halfIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      2 * Real.sinePowerHalfIntegral s := by
  exact
    Real.sinePowerIntegral_eq_two_mul_halfIntegral_of_split_reflection
      s
      (Real.sinePowerIntegral_split_at_half s hs)
      (Real.sinePowerIntegral_reflected_upperHalf_eq_half s hs)

/-- Left endpoint for the sine substitution `x = sin u`. -/
theorem Real.sinePower_sinSubstitution_leftEndpoint :
    Real.sin (0 : ℝ) = 0 :=
  Real.sin_zero

/-- Right endpoint for the sine substitution `x = sin u`. -/
theorem Real.sinePower_sinSubstitution_rightEndpoint :
    Real.sin (Real.pi / 2) = 1 :=
  Real.sin_pi_div_two

/-- Derivative used in the sine substitution `x = sin u`. -/
theorem Real.sinePower_sinSubstitution_hasDerivAt
    (u : ℝ) :
    HasDerivAt Real.sin (Real.cos u) u :=
  Real.hasDerivAt_sin u

/-- Left endpoint for the square substitution `t = x²`. -/
theorem Real.sinePower_squareSubstitution_leftEndpoint :
    (0 : ℝ) ^ 2 = 0 := by
  exact zero_pow two_ne_zero

/-- Right endpoint for the square substitution `t = x²`. -/
theorem Real.sinePower_squareSubstitution_rightEndpoint :
    (1 : ℝ) ^ 2 = 1 := by
  exact one_pow 2

/-- Derivative used in the square substitution `t = x²`. -/
theorem Real.sinePower_squareSubstitution_hasDerivAt
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x :=
    hasDerivAt_id' x
  have hmul :
      HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
    hid.mul hid
  have hpow :
      (fun y : ℝ => y ^ 2) = (fun y : ℝ => y * y) := by
    funext y
    exact pow_two y
  have hderiv : 1 * x + x * 1 = 2 * x := by
    calc
      1 * x + x * 1 = x + x := by
        exact congrArg₂ (fun a b : ℝ => a + b) (one_mul x) (mul_one x)
      _ = 2 * x := by
        exact (two_mul x).symm
  exact
    Eq.subst
      (motive := fun f : ℝ → ℝ => HasDerivAt f (2 * x) x)
      hpow.symm
      (hmul.congr_deriv hderiv)

/-- Source-side interval integrability for the sine substitution. -/
theorem Real.sinePower_sinSubstitution_source_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2) :
    IntervalIntegrable
      (fun u : ℝ => (Real.sin u) ^ s)
      MeasureTheory.volume
      (0 : ℝ)
      (Real.pi / 2) := by
  exact
    Real.sinePowerKernel_intervalIntegrable_zero_half
      s
      (Real.sinePowerExponent_gt_neg_one_of_leftParameter_pos hleft)

/-- Complex endpoint integrability for the Beta kernel with the sine-power
parameters. -/
theorem Real.sinePower_betaComplexKernel_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    IntervalIntegrable
      (fun t : ℝ =>
        (t : ℂ) ^ ((((s + 1) / 2 : ℝ) : ℂ) - 1) *
          (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) - 1))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  have hleft_complex :
      0 < Complex.re (((s + 1) / 2 : ℝ) : ℂ) := by
    calc
      0 < (s + 1) / 2 := hleft
      _ = Complex.re (((s + 1) / 2 : ℝ) : ℂ) := by
        rfl
  have hright_complex :
      0 < Complex.re (((1 / 2 : ℝ) : ℂ)) := by
    calc
      0 < (1 / 2 : ℝ) := hright
      _ = Complex.re (((1 / 2 : ℝ) : ℂ)) := by
        rfl
  exact Complex.betaIntegral_convergent hleft_complex hright_complex

/-- Transport of complex Beta-kernel endpoint integrability to the real-part
kernel on `[0,1]`. -/
theorem Real.sinePower_betaRealKernel_intervalIntegrable_from_complex
    (s : ℝ)
    (hcomplex :
      IntervalIntegrable
        (fun t : ℝ =>
          (t : ℂ) ^ ((((s + 1) / 2 : ℝ) : ℂ) - 1) *
            (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) : ℂ) - 1))
        MeasureTheory.volume
        (0 : ℝ)
        1) :
    IntervalIntegrable
      (fun t : ℝ =>
        t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  sorry

/-- The Beta-kernel endpoint integrability on `[0,1]` in real variables. -/
theorem Real.sinePower_betaRealKernel_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    IntervalIntegrable
      (fun t : ℝ =>
        t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  exact
    Real.sinePower_betaRealKernel_intervalIntegrable_from_complex
      s
      (Real.sinePower_betaComplexKernel_intervalIntegrable
        s hleft hright)

/-- Positivity of `1 - x²` on the open unit interval. -/
theorem Real.one_sub_sq_pos_of_mem_Ioo_zero_one
    {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    0 < 1 - x ^ 2 := by
  have hx0 : 0 < x :=
    hx.1
  have hx1 : x < 1 :=
    hx.2
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx0
  have hx_sq_lt_one : x ^ 2 < 1 := by
    calc
      x ^ 2 = x * x := by
        exact pow_two x
      _ < 1 * 1 := by
        exact mul_lt_mul hx1 hx1 hx_nonneg zero_lt_one
      _ = 1 := by
        exact one_mul 1
  exact sub_pos.mpr hx_sq_lt_one

/-- The inverse-square-root factor appearing in the sine substitution. -/
theorem Real.sinePower_sinSubstitution_invSqrt_eq_rpow
    {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    1 / Real.sqrt (1 - x ^ 2) =
      (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  have hpos : 0 < 1 - x ^ 2 :=
    Real.one_sub_sq_pos_of_mem_Ioo_zero_one hx
  have hnonneg : 0 ≤ 1 - x ^ 2 :=
    le_of_lt hpos
  have hexp : -(1 / 2 : ℝ) = ((-1 : ℝ) / 2) :=
    (neg_div 1 2).symm
  calc
    1 / Real.sqrt (1 - x ^ 2) =
        (Real.sqrt (1 - x ^ 2))⁻¹ := by
      exact one_div (Real.sqrt (1 - x ^ 2))
    _ = ((1 - x ^ 2) ^ (1 / 2 : ℝ))⁻¹ := by
      exact congrArg (fun y : ℝ => y⁻¹)
        (Real.sqrt_eq_rpow (1 - x ^ 2))
    _ = (1 - x ^ 2) ^ (-(1 / 2 : ℝ)) := by
      exact (Real.rpow_neg hnonneg (1 / 2 : ℝ)).symm
    _ = (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
      exact congrArg (fun e : ℝ => (1 - x ^ 2) ^ e) hexp

/-- The sine/arcsine part of the inverse sine substitution. -/
theorem Real.sinePower_sin_arcsin_rpow_eq
    (s : ℝ)
    {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (Real.sin (Real.arcsin x)) ^ s = x ^ s := by
  have hx_left : -1 ≤ x := by
    exact le_trans (neg_nonpos.mpr zero_le_one) (le_of_lt hx.1)
  have hx_right : x ≤ 1 :=
    le_of_lt hx.2
  exact congrArg (fun y : ℝ => y ^ s)
    (Real.sin_arcsin hx_left hx_right)

/-- Target-side interval integrability for the sine substitution. -/
theorem Real.sinePower_sinSubstitution_target_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    IntervalIntegrable
      (fun x : ℝ => x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  sorry

/-- Open-interval Jacobian identity for the inverse sine substitution. -/
theorem Real.sinePower_sinSubstitution_inverseJacobian_eq
    (s x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (Real.sin (Real.arcsin x)) ^ s *
        (1 / Real.sqrt (1 - x ^ 2)) =
      x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  calc
    (Real.sin (Real.arcsin x)) ^ s *
        (1 / Real.sqrt (1 - x ^ 2)) =
        x ^ s * (1 / Real.sqrt (1 - x ^ 2)) := by
      exact congrArg
        (fun y : ℝ => y * (1 / Real.sqrt (1 - x ^ 2)))
        (Real.sinePower_sin_arcsin_rpow_eq s hx)
    _ = x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
      exact congrArg
        (fun y : ℝ => x ^ s * y)
        (Real.sinePower_sinSubstitution_invSqrt_eq_rpow hx)

/-- The interval substitution theorem for `x = sin u` on `[0,π/2]`, after
isolating the endpoint integrability and open-interval Jacobian packages. -/
theorem Real.sinePower_sinSubstitution_intervalSubstitution
    (s : ℝ)
    (hsource :
      IntervalIntegrable
        (fun u : ℝ => (Real.sin u) ^ s)
        MeasureTheory.volume
        (0 : ℝ)
        (Real.pi / 2))
    (htarget :
      IntervalIntegrable
        (fun x : ℝ => x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2))
        MeasureTheory.volume
        (0 : ℝ)
        1)
    (hjac :
      ∀ x : ℝ,
        x ∈ Set.Ioo (0 : ℝ) 1 →
          (Real.sin (Real.arcsin x)) ^ s *
              (1 / Real.sqrt (1 - x ^ 2)) =
            x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) :
    Real.sinePowerHalfIntegral s =
      ∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  sorry

/-- The raw change-of-variables statement for `x = sin u` on `[0,π/2]`. -/
theorem Real.sinePower_sinSubstitution_changeOfVariables
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerHalfIntegral s =
      ∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  exact
    Real.sinePower_sinSubstitution_intervalSubstitution
      s
      (Real.sinePower_sinSubstitution_source_intervalIntegrable s hleft)
      (Real.sinePower_sinSubstitution_target_intervalIntegrable
        s hleft hright)
      (Real.sinePower_sinSubstitution_inverseJacobian_eq s)

/-- The real-variable `t = sin² u` substitution on `[0,π/2]`. -/
theorem Real.sinePowerHalfIntegral_eq_sinSubstitutionIntegral
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerHalfIntegral s =
      ∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  exact
    Real.sinePower_sinSubstitution_changeOfVariables
      s hleft hright

/-- Source-side interval integrability for the square substitution. -/
theorem Real.sinePower_squareSubstitution_source_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    IntervalIntegrable
      (fun x : ℝ => x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  exact
    Real.sinePower_sinSubstitution_target_intervalIntegrable
      s hleft hright

/-- Target-side interval integrability for the square substitution. -/
theorem Real.sinePower_squareSubstitution_target_intervalIntegrable
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    IntervalIntegrable
      (fun t : ℝ =>
        t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1))
      MeasureTheory.volume
      (0 : ℝ)
      1 := by
  exact Real.sinePower_betaRealKernel_intervalIntegrable s hleft hright

/-- The power of a square in the square substitution on `(0,1)`. -/
theorem Real.sinePower_squareSubstitution_sq_rpow_eq
    (s x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (x ^ 2) ^ (((s + 1) / 2) - 1) =
      x ^ (s - 1) := by
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx.1
  have hexp :
      (2 : ℝ) * (((s + 1) / 2) - 1) = s - 1 := by
    calc
      (2 : ℝ) * (((s + 1) / 2) - 1) =
          2 * ((s + 1) / 2) - 2 * 1 := by
        exact mul_sub 2 ((s + 1) / 2) 1
      _ = ((s + 1) / 2) * 2 - 2 := by
        exact congrArg₂
          (fun a b : ℝ => a - b)
          (mul_comm 2 ((s + 1) / 2))
          (mul_one 2)
      _ = (s + 1) - 2 := by
        exact congrArg (fun y : ℝ => y - 2)
          (div_mul_cancel₀ (s + 1) two_ne_zero)
      _ = (s + 1) - (1 + 1) := by
        exact congrArg (fun y : ℝ => (s + 1) - y)
          (two_eq_one_add_one : (2 : ℝ) = 1 + 1)
      _ = ((s + 1) - 1) - 1 := by
        exact sub_add_eq_sub_sub (s + 1) 1 1
      _ = s - 1 := by
        exact congrArg (fun y : ℝ => y - 1) (add_sub_cancel s 1)
  calc
    (x ^ 2) ^ (((s + 1) / 2) - 1) =
        (x ^ (2 : ℝ)) ^ (((s + 1) / 2) - 1) := by
      exact congrArg
        (fun y : ℝ => y ^ (((s + 1) / 2) - 1))
        (Real.rpow_natCast x 2).symm
    _ = x ^ ((2 : ℝ) * (((s + 1) / 2) - 1)) := by
      exact (Real.rpow_mul hx_nonneg 2 (((s + 1) / 2) - 1)).symm
    _ = x ^ (s - 1) := by
      exact congrArg (fun e : ℝ => x ^ e) hexp

/-- The right endpoint exponent in the square substitution. -/
theorem Real.sinePower_squareSubstitution_rightExponent_eq :
    ((1 / 2 : ℝ) - 1) = ((-1 : ℝ) / 2) := by
  calc
    (1 / 2 : ℝ) - 1 = (1 / 2 : ℝ) - (2 / 2 : ℝ) := by
      exact congrArg (fun y : ℝ => (1 / 2 : ℝ) - y)
        (by
          exact (div_self two_ne_zero).symm)
    _ = (1 - 2 : ℝ) / 2 := by
      exact (sub_div 1 2 2).symm
    _ = (1 - (1 + 1) : ℝ) / 2 := by
      exact congrArg (fun y : ℝ => (1 - y) / 2)
        (two_eq_one_add_one : (2 : ℝ) = 1 + 1)
    _ = ((1 - 1) - 1 : ℝ) / 2 := by
      exact congrArg (fun y : ℝ => y / 2)
        (sub_add_eq_sub_sub 1 1 1)
    _ = (0 - 1 : ℝ) / 2 := by
      exact congrArg (fun y : ℝ => (y - 1) / 2) (sub_self 1)
    _ = (-1 : ℝ) / 2 := by
      exact congrArg (fun y : ℝ => y / 2) (zero_sub 1)

/-- The scalar Jacobian cancellation in the square substitution. -/
theorem Real.sinePower_squareSubstitution_scalar_cancel
    (x y : ℝ) :
    ((1 / 2 : ℝ) * y) * (2 * x) = y * x := by
  have hhalf_two : (1 / 2 : ℝ) * 2 = 1 := by
    calc
      (1 / 2 : ℝ) * 2 = (2 : ℝ)⁻¹ * 2 := by
        exact congrArg (fun z : ℝ => z * 2) (one_div 2)
      _ = 1 := by
        exact inv_mul_cancel₀ two_ne_zero
  calc
    ((1 / 2 : ℝ) * y) * (2 * x) =
        (((1 / 2 : ℝ) * y) * 2) * x := by
      exact mul_assoc ((1 / 2 : ℝ) * y) 2 x
    _ = ((1 / 2 : ℝ) * (y * 2)) * x := by
      exact congrArg (fun z : ℝ => z * x)
        (mul_assoc (1 / 2 : ℝ) y 2)
    _ = ((1 / 2 : ℝ) * (2 * y)) * x := by
      exact congrArg
        (fun z : ℝ => ((1 / 2 : ℝ) * z) * x)
        (mul_comm y 2)
    _ = (((1 / 2 : ℝ) * 2) * y) * x := by
      exact congrArg (fun z : ℝ => z * x)
        (mul_assoc (1 / 2 : ℝ) 2 y).symm
    _ = (1 * y) * x := by
      exact congrArg (fun z : ℝ => (z * y) * x) hhalf_two
    _ = y * x := by
      exact congrArg (fun z : ℝ => z * x) (one_mul y)

/-- The left endpoint power algebra in the square substitution. -/
theorem Real.sinePower_squareSubstitution_leftPower_mul_eq
    (s x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    x ^ (s - 1) * x = x ^ s := by
  calc
    x ^ (s - 1) * x = x ^ (s - 1) * x ^ (1 : ℝ) := by
      exact congrArg (fun y : ℝ => x ^ (s - 1) * y)
        (Real.rpow_one x).symm
    _ = x ^ ((s - 1) + 1) := by
      exact (Real.rpow_add hx.1 (s - 1) 1).symm
    _ = x ^ s := by
      exact congrArg (fun e : ℝ => x ^ e) (sub_add_cancel s 1)

/-- Reassociation of the square-substitution integrand after the scalar
Jacobian has been cancelled. -/
theorem Real.sinePower_squareSubstitution_mul_reassociate
    (x a b : ℝ) :
    (a * b) * x = (a * x) * b := by
  calc
    (a * b) * x = a * (b * x) := by
      exact mul_assoc a b x
    _ = a * (x * b) := by
      exact congrArg (fun z : ℝ => a * z) (mul_comm b x)
    _ = (a * x) * b := by
      exact (mul_assoc a x b).symm

/-- Open-interval Jacobian identity for the square substitution `t = x²`. -/
theorem Real.sinePower_squareSubstitution_jacobian_eq
    (s x : ℝ)
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    ((1 / 2 : ℝ) *
        ((x ^ 2) ^ (((s + 1) / 2) - 1) *
          (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))) *
        (2 * x) =
      x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
  have hsq :
      (x ^ 2) ^ (((s + 1) / 2) - 1) =
        x ^ (s - 1) :=
    Real.sinePower_squareSubstitution_sq_rpow_eq s x hx
  have hright :
      (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1) =
        (1 - x ^ 2) ^ ((-1 : ℝ) / 2) :=
    congrArg
      (fun e : ℝ => (1 - x ^ 2) ^ e)
      Real.sinePower_squareSubstitution_rightExponent_eq
  calc
    ((1 / 2 : ℝ) *
        ((x ^ 2) ^ (((s + 1) / 2) - 1) *
          (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))) *
        (2 * x) =
        (((x ^ 2) ^ (((s + 1) / 2) - 1) *
          (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1)) * x) := by
      exact
        Real.sinePower_squareSubstitution_scalar_cancel
          x
          ((x ^ 2) ^ (((s + 1) / 2) - 1) *
            (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))
    _ =
        ((x ^ (s - 1) *
          (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) * x) := by
      exact congrArg
        (fun y : ℝ => y * x)
        (congrArg₂
          (fun a b : ℝ => a * b)
          hsq
          hright)
    _ =
        (x ^ (s - 1) * x) *
          (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
      exact
        Real.sinePower_squareSubstitution_mul_reassociate
          x
          (x ^ (s - 1))
          ((1 - x ^ 2) ^ ((-1 : ℝ) / 2))
    _ =
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2) := by
      exact congrArg
        (fun y : ℝ => y * (1 - x ^ 2) ^ ((-1 : ℝ) / 2))
        (Real.sinePower_squareSubstitution_leftPower_mul_eq s x hx)

/-- The interval substitution theorem for `t = x²` on `[0,1]`, after
isolating endpoint integrability and the Jacobian computation. -/
theorem Real.sinePower_squareSubstitution_intervalSubstitution
    (s : ℝ)
    (hsource :
      IntervalIntegrable
        (fun x : ℝ => x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2))
        MeasureTheory.volume
        (0 : ℝ)
        1)
    (htarget :
      IntervalIntegrable
        (fun t : ℝ =>
          t ^ (((s + 1) / 2) - 1) *
            (1 - t) ^ ((1 / 2 : ℝ) - 1))
        MeasureTheory.volume
        (0 : ℝ)
        1)
    (hjac :
      ∀ x : ℝ,
        x ∈ Set.Ioo (0 : ℝ) 1 →
          ((1 / 2 : ℝ) *
              ((x ^ 2) ^ (((s + 1) / 2) - 1) *
                (1 - x ^ 2) ^ ((1 / 2 : ℝ) - 1))) *
              (2 * x) =
            x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) :
    (∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaRealIntegral s := by
  sorry

/-- The raw change-of-variables statement for `t = x²` on `[0,1]`. -/
theorem Real.sinePower_squareSubstitution_changeOfVariables
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    (∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaRealIntegral s := by
  exact
    Real.sinePower_squareSubstitution_intervalSubstitution
      s
      (Real.sinePower_squareSubstitution_source_intervalIntegrable
        s hleft hright)
      (Real.sinePower_squareSubstitution_target_intervalIntegrable
        s hleft hright)
      (Real.sinePower_squareSubstitution_jacobian_eq s)

/-- The real-variable `t = x²` substitution converting the sine-substitution
integral into the unit-interval Beta integral. -/
theorem Real.sinePowerSinSubstitutionIntegral_eq_half_betaRealIntegral
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    (∫ x in (0 : ℝ)..1,
        x ^ s * (1 - x ^ 2) ^ ((-1 : ℝ) / 2)) =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaRealIntegral s := by
  exact
    Real.sinePower_squareSubstitution_changeOfVariables
      s hleft hright

/-- The real-variable `t = sin² u` substitution on `[0,π/2]`. -/
theorem Real.sinePowerHalfIntegral_eq_half_betaRealIntegral_from_sinSqSubstitution
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerHalfIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaRealIntegral s := by
  exact
    Eq.trans
      (Real.sinePowerHalfIntegral_eq_sinSubstitutionIntegral
        s hleft hright)
      (Real.sinePowerSinSubstitutionIntegral_eq_half_betaRealIntegral
        s hleft hright)

/-- Real/complex comparison for the unit-interval Beta integrand, using
`Complex.ofReal_cpow` on the positive interval `(0,1)`. -/
/-- Pointwise real-part comparison for the unit-interval Beta integrands. -/
theorem Real.sinePowerEulerBetaReal_integrand_re_eq
    (s t : ℝ)
    (ht0 : 0 ≤ t)
    (ht1 : 0 ≤ 1 - t) :
    ((t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
        (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ)).re =
      t ^ (((s + 1) / 2) - 1) *
        (1 - t) ^ ((1 / 2 : ℝ) - 1) := by
  have ht_cpow :
      ((t ^ (((s + 1) / 2) - 1) : ℝ) : ℂ) =
        (t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) :=
    Complex.ofReal_cpow ht0 (((s + 1) / 2) - 1)
  have h1_cpow :
      (((1 - t) ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) =
        ((1 - t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) :=
    Complex.ofReal_cpow ht1 ((1 / 2 : ℝ) - 1)
  have hsub_coe : ((1 - t : ℝ) : ℂ) = 1 - (t : ℂ) := by
    exact Complex.ofReal_sub 1 t
  have hprod :
      (((t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)) =
        (t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
          (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) := by
    calc
      (((t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)) =
          ((t ^ (((s + 1) / 2) - 1) : ℝ) : ℂ) *
            (((1 - t) ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ) := by
        exact Complex.ofReal_mul
          (t ^ (((s + 1) / 2) - 1))
          ((1 - t) ^ ((1 / 2 : ℝ) - 1))
      _ =
          (t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
            (((1 - t : ℝ) : ℂ) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ)) := by
        exact congrArg₂ (fun a b : ℂ => a * b) ht_cpow h1_cpow
      _ =
          (t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
            (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ =>
            (t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
              z ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ))
          hsub_coe
  calc
    ((t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
        (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ)).re =
        (((t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1) : ℝ) : ℂ)).re := by
      exact congrArg Complex.re hprod.symm
    _ =
      t ^ (((s + 1) / 2) - 1) *
        (1 - t) ^ ((1 / 2 : ℝ) - 1) := by
      exact Complex.ofReal_re
        (t ^ (((s + 1) / 2) - 1) *
          (1 - t) ^ ((1 / 2 : ℝ) - 1))

/-- Integral-level real/complex comparison for the unit-interval Beta
integrand. The remaining work is transporting real part through the improper
endpoint integral. -/
theorem Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral_from_integralRe
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerEulerBetaRealIntegral s =
      Real.sinePowerEulerBetaIntegral s := by
  let a : ℂ := (((s + 1) / 2 : ℝ) : ℂ)
  let b : ℂ := (((1 / 2 : ℝ) : ℝ) : ℂ)
  let F : ℝ → ℂ :=
    fun t : ℝ =>
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)
  have ha : 0 < Complex.re a := by
    calc
      0 < (s + 1) / 2 := hleft
      _ = Complex.re a := by
        rfl
  have hb : 0 < Complex.re b := by
    calc
      0 < (1 / 2 : ℝ) := hright
      _ = Complex.re b := by
        rfl
  have hF_int :
      IntervalIntegrable F MeasureTheory.volume (0 : ℝ) 1 :=
    Complex.betaIntegral_convergent ha hb
  have hreal_eq_re :
      Real.sinePowerEulerBetaRealIntegral s =
        ∫ t in (0 : ℝ)..1, (F t).re := by
    unfold Real.sinePowerEulerBetaRealIntegral
    exact
      intervalIntegral.integral_congr
        (fun t ht => by
          have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
            rwa [Set.uIcc_of_le zero_le_one] at ht
          have ht0 : 0 ≤ t := htIcc.1
          have ht1 : 0 ≤ 1 - t :=
            sub_nonneg.mpr htIcc.2
          have ha_exp :
              a - 1 = ((((s + 1) / 2) - 1 : ℝ) : ℂ) := by
            calc
              a - 1 =
                  (((s + 1) / 2 : ℝ) : ℂ) - ((1 : ℝ) : ℂ) := by
                rfl
              _ = ((((s + 1) / 2) - 1 : ℝ) : ℂ) := by
                exact (Complex.ofReal_sub ((s + 1) / 2) 1).symm
          have hb_exp :
              b - 1 = (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) := by
            calc
              b - 1 =
                  (((1 / 2 : ℝ) : ℝ) : ℂ) - ((1 : ℝ) : ℂ) := by
                rfl
              _ = (((1 / 2 : ℝ) - 1 : ℝ) : ℂ) := by
                exact (Complex.ofReal_sub (1 / 2 : ℝ) 1).symm
          have hF_point :
              (F t).re =
                ((t : ℂ) ^ ((((s + 1) / 2) - 1 : ℝ) : ℂ) *
                  (1 - (t : ℂ)) ^ (((1 / 2 : ℝ) - 1 : ℝ) : ℂ)).re := by
            exact congrArg Complex.re
              (congrArg₂
                (fun x y : ℂ => x * y)
                (congrArg (fun z : ℂ => (t : ℂ) ^ z) ha_exp)
                (congrArg (fun z : ℂ => (1 - (t : ℂ)) ^ z) hb_exp))
          have hpoint :
              (F t).re =
                t ^ (((s + 1) / 2) - 1) *
                  (1 - t) ^ ((1 / 2 : ℝ) - 1) := by
            exact
              Eq.trans hF_point
                (Real.sinePowerEulerBetaReal_integrand_re_eq s t ht0 ht1)
          exact hpoint.symm)
  have hre_transport :
      (∫ t in (0 : ℝ)..1, (F t).re) =
        (∫ t in (0 : ℝ)..1, F t).re := by
    exact
      (@RCLike.reCLM ℂ _).intervalIntegral_comp_comm hF_int
  have hbeta_unfold :
      (∫ t in (0 : ℝ)..1, F t) =
        Complex.betaIntegral a b := by
    rfl
  calc
    Real.sinePowerEulerBetaRealIntegral s =
        ∫ t in (0 : ℝ)..1, (F t).re := hreal_eq_re
    _ = (∫ t in (0 : ℝ)..1, F t).re := hre_transport
    _ = (Complex.betaIntegral a b).re := by
      exact congrArg Complex.re hbeta_unfold
    _ = Real.sinePowerEulerBetaIntegral s := by
      rfl

/-- Real/complex comparison for the unit-interval Beta integrand, using
`Complex.ofReal_cpow` on the positive interval `(0,1)`. -/
theorem Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral_from_ofRealCpow
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerEulerBetaRealIntegral s =
      Real.sinePowerEulerBetaIntegral s := by
  exact
    Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral_from_integralRe
      s hleft hright

/-- Identification of the real unit-interval Beta integral with the real part
of mathlib's complex Beta integral. -/
theorem Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerEulerBetaRealIntegral s =
      Real.sinePowerEulerBetaIntegral s := by
  exact
    Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral_from_ofRealCpow
      s hleft hright

/-- Multiplying the unit-interval Beta identification by the half-factor. -/
theorem Real.sinePowerHalfIntegral_betaRealIntegral_eq_eulerBetaIntegral
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    (1 / 2 : ℝ) * Real.sinePowerEulerBetaRealIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s := by
  exact congrArg
    (fun x : ℝ => (1 / 2 : ℝ) * x)
    (Real.sinePowerEulerBetaRealIntegral_eq_eulerBetaIntegral s hleft hright)

/-- The Euler-Beta substitution for the lower half-interval after the
parameters have been proved positive. -/
theorem Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral_from_sinSqSubstitution
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerHalfIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s := by
  exact
    Eq.trans
      (Real.sinePowerHalfIntegral_eq_half_betaRealIntegral_from_sinSqSubstitution
        s hleft hright)
      (Real.sinePowerHalfIntegral_betaRealIntegral_eq_eulerBetaIntegral
        s hleft hright)

/-- Euler-Beta substitution for the half sine-power integral with explicit
positive Beta parameters. -/
theorem Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral_of_posParameters
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerHalfIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s := by
  exact
    Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral_from_sinSqSubstitution
      s hleft hright

/-- Euler-Beta substitution for the half sine-power integral. -/
theorem Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerHalfIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s := by
  exact
    Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral_of_posParameters
      s
      (Real.sinePowerEulerBeta_leftParameter_pos hs)
      Real.sinePowerEulerBeta_rightParameter_pos

/-- The sine-power integral is the Euler-Beta integral. -/
theorem Real.sinePowerIntegral_eq_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      Real.sinePowerEulerBetaIntegral s := by
  have hsplit :
      Real.sinePowerIntegral s =
        2 * Real.sinePowerHalfIntegral s :=
    Real.sinePowerIntegral_eq_two_mul_halfIntegral s hs
  have hbeta :
      Real.sinePowerHalfIntegral s =
        (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s :=
    Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral s hs
  calc
    Real.sinePowerIntegral s =
        2 * Real.sinePowerHalfIntegral s := hsplit
    _ = 2 * ((1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s) := by
      exact congrArg (fun x : ℝ => 2 * x) hbeta
    _ = Real.sinePowerEulerBetaIntegral s := by
      exact Real.two_mul_one_half_mul (Real.sinePowerEulerBetaIntegral s)

/-- Complex Beta/Gamma comparison after dividing by the nonzero Gamma value at
the sum of the two positive real parameters. -/
theorem Real.sinePowerEulerBetaIntegral_eq_gammaQuotient_re_from_complexBetaGamma
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerEulerBetaIntegral s =
      (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
          Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re := by
  let a : ℂ := (((s + 1) / 2 : ℝ) : ℂ)
  let b : ℂ := (((1 / 2 : ℝ) : ℝ) : ℂ)
  have ha : 0 < Complex.re a := by
    calc
      0 < (s + 1) / 2 := hleft
      _ = Complex.re a := by
        rfl
  have hb : 0 < Complex.re b := by
    calc
      0 < (1 / 2 : ℝ) := hright
      _ = Complex.re b := by
        rfl
  have hsum_pos : 0 < Complex.re (a + b) := by
    exact add_pos ha hb
  have hsum_ne : Complex.Gamma (a + b) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hsum_pos
  have hmul :
      Complex.Gamma a * Complex.Gamma b =
        Complex.Gamma (a + b) * Complex.betaIntegral a b :=
    Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hbeta :
      Complex.betaIntegral a b =
        Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
    exact
      (eq_div_iff hsum_ne).mpr
        (Eq.trans (mul_comm (Complex.Gamma (a + b)) (Complex.betaIntegral a b)) hmul.symm)
  calc
    Real.sinePowerEulerBetaIntegral s =
        (Complex.betaIntegral a b).re := by
      rfl
    _ =
        (Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b)).re := by
      exact congrArg Complex.re hbeta
    _ =
        (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
            Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
          Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re := by
      rfl

/-- Real Gamma at `1/2` in the normalization used by the sine-power formula. -/
theorem Real.Gamma_one_half_eq_sqrt_pi :
    Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := by
  exact Real.Gamma_one_half_eq

/-- Complex Gamma on positive real inputs has real part equal to real Gamma in
the normalization used by this file. -/
theorem Real.Complex_Gamma_ofReal_re_eq_Real_Gamma_of_pos
    {x : ℝ}
    (hx : 0 < x) :
    (Complex.Gamma (x : ℂ)).re = Real.Gamma x := by
  calc
    (Complex.Gamma (x : ℂ)).re = ((Real.Gamma x : ℝ) : ℂ).re := by
      exact congrArg Complex.re (Complex.Gamma_ofReal x)
    _ = Real.Gamma x := by
      exact Complex.ofReal_re (Real.Gamma x)

/-- Complex Beta/Gamma comparison specialized to the sine-power parameters,
before taking real Gamma normalizations. -/
theorem Real.sinePowerEulerBetaIntegral_eq_gammaQuotient_re_of_posParameters
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ)) :
    Real.sinePowerEulerBetaIntegral s =
    (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
          Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re := by
  exact
    Real.sinePowerEulerBetaIntegral_eq_gammaQuotient_re_from_complexBetaGamma
      s hleft hright

/-- Conversion of the complex Gamma quotient to the real Gamma-ratio after all
real/complex Gamma coercions and the `Γ(1/2)` normalization are exposed. -/
theorem Real.sinePowerGammaQuotient_re_eq_gammaRatio_from_realCoercions
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ))
    (hsum : (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1) :
    (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
          Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re =
      Real.sinePowerGammaRatio s := by
  have hleft_coe :
      Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) =
        ((Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal ((s + 1) / 2)
  have hright_coe :
      Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) =
        ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) :=
    Complex.Gamma_ofReal (1 / 2 : ℝ)
  have hsum_coe :
      Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ) =
        ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ) := by
    calc
      Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ) =
          ((Real.Gamma (((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℝ) : ℂ) := by
        exact Complex.Gamma_ofReal (((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ)
      _ = ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ) := by
        exact congrArg (fun x : ℝ => ((Real.Gamma x : ℝ) : ℂ)) hsum
  have hquotient_ofReal :
      (((Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) *
            ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
          ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)) =
        ((Real.Gamma ((s + 1) / 2) *
            Real.Gamma (1 / 2 : ℝ) /
          Real.Gamma (s / 2 + 1) : ℝ) : ℂ) := by
    calc
      (((Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) *
            ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
          ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)) =
          ((Real.Gamma ((s + 1) / 2) *
              Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
            ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ) := by
        exact congrArg
          (fun z : ℂ => z / ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ))
          (Complex.ofReal_mul
            (Real.Gamma ((s + 1) / 2))
            (Real.Gamma (1 / 2 : ℝ))).symm
      _ =
          ((Real.Gamma ((s + 1) / 2) *
              Real.Gamma (1 / 2 : ℝ) /
            Real.Gamma (s / 2 + 1) : ℝ) : ℂ) := by
        exact
          (Complex.ofReal_div
            (Real.Gamma ((s + 1) / 2) *
              Real.Gamma (1 / 2 : ℝ))
            (Real.Gamma (s / 2 + 1))).symm
  calc
    (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
          Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re =
        (((Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) *
            ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
          ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re := by
      have hden :
          (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
              Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re =
            (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
              ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re := by
        exact congrArg Complex.re
          (congrArg
            (fun z : ℂ =>
              Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) / z)
            hsum_coe)
      have hright' :
          (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
              ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re =
            (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
              ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re := by
        exact congrArg Complex.re
          (congrArg
            (fun z : ℂ =>
              Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) * z /
                ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ))
            hright_coe)
      have hleft' :
          (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
                ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
              ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re =
            (((Real.Gamma ((s + 1) / 2) : ℝ) : ℂ) *
                ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
              ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ)).re := by
        exact congrArg Complex.re
          (congrArg
            (fun z : ℂ =>
              z * ((Real.Gamma (1 / 2 : ℝ) : ℝ) : ℂ) /
                ((Real.Gamma (s / 2 + 1) : ℝ) : ℂ))
            hleft_coe)
      exact Eq.trans hden (Eq.trans hright' hleft')
    _ =
        (Real.Gamma ((s + 1) / 2) *
            Real.Gamma (1 / 2 : ℝ) /
          Real.Gamma (s / 2 + 1)) := by
      exact Eq.trans
        (congrArg Complex.re hquotient_ofReal)
        (Complex.ofReal_re
        (Real.Gamma ((s + 1) / 2) *
          Real.Gamma (1 / 2 : ℝ) /
        Real.Gamma (s / 2 + 1)))
    _ =
        Real.sinePowerGammaRatio s := by
      calc
        Real.Gamma ((s + 1) / 2) *
            Real.Gamma (1 / 2 : ℝ) /
          Real.Gamma (s / 2 + 1) =
            Real.Gamma ((s + 1) / 2) *
              Real.sqrt Real.pi /
            Real.Gamma (s / 2 + 1) := by
          exact congrArg
            (fun x : ℝ =>
              Real.Gamma ((s + 1) / 2) * x /
                Real.Gamma (s / 2 + 1))
            Real.Gamma_one_half_eq_sqrt_pi
        _ =
            Real.sqrt Real.pi *
              Real.Gamma ((s + 1) / 2) /
            Real.Gamma (s / 2 + 1) := by
          exact congrArg
            (fun x : ℝ => x / Real.Gamma (s / 2 + 1))
            (mul_comm (Real.Gamma ((s + 1) / 2)) (Real.sqrt Real.pi))
        _ = Real.sinePowerGammaRatio s := by
          rfl

/-- Real-part conversion of the complex Gamma quotient to the real Gamma-ratio
normalization used by the sine-power integral. -/
theorem Real.sinePowerGammaQuotient_re_eq_gammaRatio
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ))
    (hsum : (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1) :
    (Complex.Gamma (((s + 1) / 2 : ℝ) : ℂ) *
          Complex.Gamma (((1 / 2 : ℝ) : ℝ) : ℂ) /
        Complex.Gamma ((((s + 1) / 2 + (1 / 2 : ℝ)) : ℝ) : ℂ)).re =
      Real.sinePowerGammaRatio s := by
  exact
    Real.sinePowerGammaQuotient_re_eq_gammaRatio_from_realCoercions
      s hleft hright hsum

/-- Beta/Gamma comparison with the positive parameters exposed. -/
theorem Real.sinePowerEulerBetaIntegral_eq_gammaRatio_of_posParameters
    (s : ℝ)
    (hleft : 0 < (s + 1) / 2)
    (hright : 0 < (1 / 2 : ℝ))
    (hsum : (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1) :
    Real.sinePowerEulerBetaIntegral s =
      Real.sinePowerGammaRatio s := by
  exact
    Eq.trans
      (Real.sinePowerEulerBetaIntegral_eq_gammaQuotient_re_of_posParameters
        s hleft hright)
      (Real.sinePowerGammaQuotient_re_eq_gammaRatio
        s hleft hright hsum)

/-- Beta/Gamma comparison for the sine-power Euler-Beta integral. -/
theorem Real.sinePowerEulerBetaIntegral_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerEulerBetaIntegral s =
      Real.sinePowerGammaRatio s := by
  have hleft : 0 < (s + 1) / 2 :=
    Real.sinePowerEulerBeta_leftParameter_pos hs
  have hright : 0 < (1 / 2 : ℝ) :=
    Real.sinePowerEulerBeta_rightParameter_pos
  have hsum :
      (s + 1) / 2 + (1 / 2 : ℝ) = s / 2 + 1 :=
    Real.sinePowerEulerBeta_parameter_sum s
  exact
    Real.sinePowerEulerBetaIntegral_eq_gammaRatio_of_posParameters
      s hleft hright hsum

/-- Beta/Gamma evaluation of the sine-power integral. -/
theorem Real.sinePowerIntegral_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      Real.sinePowerGammaRatio s := by
  exact
    Eq.trans
      (Real.sinePowerIntegral_eq_eulerBetaIntegral s hs)
      (Real.sinePowerEulerBetaIntegral_eq_gammaRatio s hs)

/-- The derivative value for a positive constant base in the exponent variable
at exponent `0`. -/
theorem Real.sinePowerKernel_exponent_derivativeValue
    {a : ℝ}
    (ha : 0 < a) :
    (0 : ℝ) * (0 : ℝ) * a ^ ((0 : ℝ) - 1) +
        (1 : ℝ) * a ^ (0 : ℝ) * Real.log a =
      Real.log a := by
  have hzero_factor :
      (0 : ℝ) * (0 : ℝ) * a ^ ((0 : ℝ) - 1) = 0 := by
    calc
      (0 : ℝ) * (0 : ℝ) * a ^ ((0 : ℝ) - 1) =
          (0 : ℝ) * a ^ ((0 : ℝ) - 1) := by
        exact congrArg
          (fun x : ℝ => x * a ^ ((0 : ℝ) - 1))
          (zero_mul (0 : ℝ))
      _ = 0 := by
        exact zero_mul (a ^ ((0 : ℝ) - 1))
  calc
    (0 : ℝ) * (0 : ℝ) * a ^ ((0 : ℝ) - 1) +
        (1 : ℝ) * a ^ (0 : ℝ) * Real.log a =
        0 + (1 : ℝ) * a ^ (0 : ℝ) * Real.log a := by
      exact congrArg
        (fun x : ℝ => x + (1 : ℝ) * a ^ (0 : ℝ) * Real.log a)
        hzero_factor
    _ = (1 : ℝ) * a ^ (0 : ℝ) * Real.log a := by
      exact zero_add ((1 : ℝ) * a ^ (0 : ℝ) * Real.log a)
    _ = a ^ (0 : ℝ) * Real.log a := by
      exact congrArg
        (fun x : ℝ => x * Real.log a)
        (one_mul (a ^ (0 : ℝ)))
    _ = 1 * Real.log a := by
      exact congrArg (fun x : ℝ => x * Real.log a) (Real.rpow_zero a)
    _ = Real.log a := by
      exact one_mul (Real.log a)

/-- Pointwise derivative of the sine-power kernel with respect to the exponent
at an interior point of `[0,π]`. -/
theorem Real.sinePowerKernel_exponent_hasDerivAt_zero
    (u : ℝ)
    (hu0 : 0 < u)
    (hupi : u < Real.pi) :
    HasDerivAt
      (fun s : ℝ => (Real.sin u) ^ s)
      (Real.log (Real.sin u))
      0 := by
  have hsin_pos : 0 < Real.sin u :=
    Real.sin_pos_of_pos_of_lt_pi hu0 hupi
  have hbase :
      HasDerivAt (fun _ : ℝ => Real.sin u) 0 (0 : ℝ) :=
    hasDerivAt_const (0 : ℝ) (Real.sin u)
  have hexponent :
      HasDerivAt (fun s : ℝ => s) 1 (0 : ℝ) :=
    hasDerivAt_id' (0 : ℝ)
  have hraw :
      HasDerivAt
        (fun s : ℝ => (Real.sin u) ^ s)
        ((0 : ℝ) * (0 : ℝ) * (Real.sin u) ^ ((0 : ℝ) - 1) +
          (1 : ℝ) * (Real.sin u) ^ (0 : ℝ) *
            Real.log (Real.sin u))
        0 :=
    hbase.rpow hexponent hsin_pos
  exact
    hraw.congr_deriv
      (Real.sinePowerKernel_exponent_derivativeValue hsin_pos)

/-- Differentiation under the integral for the sine-power family at exponent
`0`, after pointwise differentiation and endpoint domination have been
established. -/
theorem Real.sinePowerIntegral_hasDerivAt_zero_from_pointwiseDerivative_and_domination :
    HasDerivAt
      Real.sinePowerIntegral
      (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
      0 := by
  sorry

/-- Differentiating the sine-power integral at exponent `0`. -/
theorem Real.sinePowerIntegral_hasDerivAt_zero_from_differentiationUnderIntegral :
    HasDerivAt
      Real.sinePowerIntegral
      (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
      0 := by
  exact
    Real.sinePowerIntegral_hasDerivAt_zero_from_pointwiseDerivative_and_domination

/-- Differentiating the sine-power integral at exponent `0`. -/
theorem Real.sinePowerIntegral_hasDerivAt_zero :
    HasDerivAt
      Real.sinePowerIntegral
      (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
      0 := by
  exact Real.sinePowerIntegral_hasDerivAt_zero_from_differentiationUnderIntegral

/-- Legendre duplication differentiated logarithmically at `1/2`. -/
theorem Real.gammaLogDeriv_one_sub_half_eq_two_log_two_from_duplicationDerivative :
    Real.gammaLogDeriv 1 - Real.gammaLogDeriv (1 / 2) =
      2 * Real.log 2 := by
  sorry

/-- Legendre duplication in logarithmic-derivative form at `1/2`. -/
theorem Real.gammaLogDeriv_one_sub_half_eq_two_log_two :
    Real.gammaLogDeriv 1 - Real.gammaLogDeriv (1 / 2) =
      2 * Real.log 2 := by
  exact Real.gammaLogDeriv_one_sub_half_eq_two_log_two_from_duplicationDerivative

/-- Reversed Legendre log-derivative difference at the half-point. -/
theorem Real.gammaLogDeriv_half_sub_one_eq_neg_two_log_two :
    Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1 =
      -(2 * Real.log 2) := by
  calc
    Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1 =
        -(Real.gammaLogDeriv 1 - Real.gammaLogDeriv (1 / 2)) := by
      exact sub_eq_neg_sub (Real.gammaLogDeriv (1 / 2)) (Real.gammaLogDeriv 1)
    _ = -(2 * Real.log 2) := by
      exact congrArg Neg.neg Real.gammaLogDeriv_one_sub_half_eq_two_log_two

/-- The Gamma-ratio derivative value after inserting Legendre duplication. -/
theorem Real.sinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two :
    Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2) =
      -Real.pi * Real.log 2 := by
  calc
    Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2) =
        Real.pi * (-(2 * Real.log 2) / 2) := by
      exact congrArg
        (fun x : ℝ => Real.pi * (x / 2))
        Real.gammaLogDeriv_half_sub_one_eq_neg_two_log_two
    _ = Real.pi * (-(Real.log 2)) := by
      exact congrArg
        (fun x : ℝ => Real.pi * x)
        (neg_mul_div_two_cancel (Real.log 2))
    _ = -Real.pi * Real.log 2 := by
      exact neg_mul_eq_neg_mul Real.pi (Real.log 2)

/-- Value of the Gamma-ratio at exponent `0`. -/
theorem Real.sinePowerGammaRatio_zero_eq_pi :
    Real.sinePowerGammaRatio 0 = Real.pi := by
  have hnum_arg : (((0 : ℝ) + 1) / 2) = (1 / 2 : ℝ) := by
    exact congrArg (fun x : ℝ => x / 2) (zero_add 1)
  have hden_arg : (0 : ℝ) / 2 + 1 = (1 : ℝ) := by
    calc
      (0 : ℝ) / 2 + 1 = 0 + 1 := by
        exact congrArg (fun x : ℝ => x + 1) (zero_div 2)
      _ = 1 := by
        exact zero_add 1
  calc
    Real.sinePowerGammaRatio 0 =
        Real.sqrt Real.pi *
          Real.Gamma (((0 : ℝ) + 1) / 2) /
            Real.Gamma ((0 : ℝ) / 2 + 1) := by
      rfl
    _ =
        Real.sqrt Real.pi *
          Real.Gamma (1 / 2 : ℝ) /
            Real.Gamma (1 : ℝ) := by
      exact congrArg₂
        (fun x y : ℝ => Real.sqrt Real.pi * Real.Gamma x / Real.Gamma y)
        hnum_arg
        hden_arg
    _ =
        Real.sqrt Real.pi *
          Real.sqrt Real.pi /
            Real.Gamma (1 : ℝ) := by
      exact congrArg
        (fun x : ℝ => Real.sqrt Real.pi * x / Real.Gamma (1 : ℝ))
        Real.Gamma_one_half_eq_sqrt_pi
    _ =
        Real.sqrt Real.pi *
          Real.sqrt Real.pi /
            1 := by
      exact congrArg
        (fun x : ℝ => Real.sqrt Real.pi * Real.sqrt Real.pi / x)
        Real.Gamma_one
    _ =
        Real.sqrt Real.pi * Real.sqrt Real.pi := by
      exact div_one (Real.sqrt Real.pi * Real.sqrt Real.pi)
    _ =
        Real.pi := by
      calc
        Real.sqrt Real.pi * Real.sqrt Real.pi =
            (Real.sqrt Real.pi) ^ 2 := by
          exact (pow_two (Real.sqrt Real.pi)).symm
        _ = Real.pi := by
          exact Real.sq_sqrt Real.pi_pos.le

/-- Derivative of the numerator Gamma factor in the sine-power Gamma-ratio. -/
theorem Real.sinePowerGammaRatio_numeratorGamma_hasDerivAt_zero :
    HasDerivAt
      (fun s : ℝ => Real.Gamma ((s + 1) / 2))
      ((1 / 2 : ℝ) * deriv Real.Gamma (1 / 2))
      0 := by
  have hgamma :
      HasDerivAt Real.Gamma (deriv Real.Gamma (1 / 2)) (1 / 2) :=
    (Real.differentiableAt_Gamma
      (fun m : ℕ => by
        have hneg_nonpos : -(m : ℝ) ≤ 0 :=
          neg_nonpos.mpr (Nat.cast_nonneg m)
        have hpos : (0 : ℝ) < 1 / 2 :=
          one_half_pos
        exact ne_of_gt (lt_of_le_of_lt hneg_nonpos hpos))).hasDerivAt
  have haffine :
      HasDerivAt (fun s : ℝ => (s + 1) / 2) (1 / 2 : ℝ) 0 := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 (0 : ℝ) :=
      hasDerivAt_id' (0 : ℝ)
    have hadd : HasDerivAt (fun s : ℝ => s + 1) 1 (0 : ℝ) :=
      hid.add_const 1
    exact hadd.div_const 2
  have hcomp :
      HasDerivAt
        (Real.Gamma ∘ fun s : ℝ => (s + 1) / 2)
        (deriv Real.Gamma (1 / 2) * (1 / 2 : ℝ))
        0 :=
    hgamma.comp (0 : ℝ) haffine
  exact hcomp.congr_deriv (mul_comm (deriv Real.Gamma (1 / 2)) (1 / 2 : ℝ))

/-- Derivative of the denominator Gamma factor in the sine-power Gamma-ratio. -/
theorem Real.sinePowerGammaRatio_denominatorGamma_hasDerivAt_zero :
    HasDerivAt
      (fun s : ℝ => Real.Gamma (s / 2 + 1))
      ((1 / 2 : ℝ) * deriv Real.Gamma 1)
      0 := by
  have hgamma :
      HasDerivAt Real.Gamma (deriv Real.Gamma 1) 1 :=
    (Real.differentiableAt_Gamma
      (fun m : ℕ => by
        have hneg_nonpos : -(m : ℝ) ≤ 0 :=
          neg_nonpos.mpr (Nat.cast_nonneg m)
        exact ne_of_gt (lt_of_le_of_lt hneg_nonpos zero_lt_one))).hasDerivAt
  have haffine :
      HasDerivAt (fun s : ℝ => s / 2 + 1) (1 / 2 : ℝ) 0 := by
    have hid : HasDerivAt (fun s : ℝ => s) 1 (0 : ℝ) :=
      hasDerivAt_id' (0 : ℝ)
    have hdiv : HasDerivAt (fun s : ℝ => s / 2) (1 / 2 : ℝ) 0 :=
      hid.div_const 2
    exact hdiv.add_const 1
  have hcomp :
      HasDerivAt
        (Real.Gamma ∘ fun s : ℝ => s / 2 + 1)
        (deriv Real.Gamma 1 * (1 / 2 : ℝ))
        0 :=
    hgamma.comp (0 : ℝ) haffine
  exact hcomp.congr_deriv (mul_comm (deriv Real.Gamma 1) (1 / 2 : ℝ))

/-- Nonvanishing of the denominator Gamma factor at exponent `0`. -/
theorem Real.sinePowerGammaRatio_denominatorGamma_zero_ne :
    Real.Gamma ((0 : ℝ) / 2 + 1) ≠ 0 :=
  Real.Gamma_ne_zero_of_pos
    Real.sinePowerGammaRatio_denominatorParameter_zero_pos

/-- Algebraic normalization of the quotient-rule derivative for the
sine-power Gamma-ratio at exponent `0`. -/
theorem Real.sinePowerGammaRatio_quotientRule_derivativeValue :
    ((Real.sqrt Real.pi *
          ((1 / 2 : ℝ) * deriv Real.Gamma (1 / 2)) *
        Real.Gamma ((0 : ℝ) / 2 + 1) -
      (Real.sqrt Real.pi *
          Real.Gamma (((0 : ℝ) + 1) / 2)) *
        ((1 / 2 : ℝ) * deriv Real.Gamma 1)) /
      Real.Gamma ((0 : ℝ) / 2 + 1) ^ 2 =
      Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2) := by
  have hnum_arg : (((0 : ℝ) + 1) / 2) = (1 / 2 : ℝ) := by
    exact congrArg (fun x : ℝ => x / 2) (zero_add 1)
  have hden_arg : (0 : ℝ) / 2 + 1 = (1 : ℝ) := by
    calc
      (0 : ℝ) / 2 + 1 = 0 + 1 := by
        exact congrArg (fun x : ℝ => x + 1) (zero_div 2)
      _ = 1 := by
        exact zero_add 1
  have hsqrt_sq :
      Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := by
    calc
      Real.sqrt Real.pi * Real.sqrt Real.pi =
          (Real.sqrt Real.pi) ^ 2 := by
        exact (pow_two (Real.sqrt Real.pi)).symm
      _ = Real.pi := by
        exact Real.sq_sqrt Real.pi_pos.le
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [hnum_arg, hden_arg, Real.Gamma_one, Real.Gamma_one_half_eq_sqrt_pi,
    Real.gammaLogDeriv]
  rw [Real.Gamma_one, Real.Gamma_one_half_eq_sqrt_pi]
  field_simp [hsqrt_ne]
  rw [hsqrt_sq]
  ring

/-- Quotient-rule assembly of the sine-power Gamma-ratio derivative from its
component Gamma derivatives. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero_from_quotientRule :
    HasDerivAt
      Real.sinePowerGammaRatio
      (Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
      0 := by
  have hnum :
      HasDerivAt
        (fun s : ℝ => Real.sqrt Real.pi * Real.Gamma ((s + 1) / 2))
        (Real.sqrt Real.pi *
          ((1 / 2 : ℝ) * deriv Real.Gamma (1 / 2)))
        0 :=
    Real.sinePowerGammaRatio_numeratorGamma_hasDerivAt_zero.const_mul
      (Real.sqrt Real.pi)
  have hden :
      HasDerivAt
        (fun s : ℝ => Real.Gamma (s / 2 + 1))
        ((1 / 2 : ℝ) * deriv Real.Gamma 1)
        0 :=
    Real.sinePowerGammaRatio_denominatorGamma_hasDerivAt_zero
  have hraw :
      HasDerivAt
        (fun s : ℝ =>
          (Real.sqrt Real.pi * Real.Gamma ((s + 1) / 2)) /
            Real.Gamma (s / 2 + 1))
        (((Real.sqrt Real.pi *
              ((1 / 2 : ℝ) * deriv Real.Gamma (1 / 2))) *
            Real.Gamma ((0 : ℝ) / 2 + 1) -
          (Real.sqrt Real.pi *
              Real.Gamma (((0 : ℝ) + 1) / 2)) *
            ((1 / 2 : ℝ) * deriv Real.Gamma 1)) /
          Real.Gamma ((0 : ℝ) / 2 + 1) ^ 2)
        0 :=
    hnum.div hden Real.sinePowerGammaRatio_denominatorGamma_zero_ne
  exact
    hraw.congr_deriv
      Real.sinePowerGammaRatio_quotientRule_derivativeValue

/-- Component-wise differentiation of the sine-power Gamma-ratio at exponent
`0`, before inserting the Legendre duplication value. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero_from_componentDerivatives :
    HasDerivAt
      Real.sinePowerGammaRatio
      (Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
      0 := by
  exact Real.sinePowerGammaRatio_hasDerivAt_zero_from_quotientRule

/-- Derivative of the sine-power Gamma-ratio in logarithmic-derivative form. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero_from_logDeriv :
    HasDerivAt
      Real.sinePowerGammaRatio
      (Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
      0 := by
  exact
    Real.sinePowerGammaRatio_hasDerivAt_zero_from_componentDerivatives

/-- Derivative of the Gamma-ratio representation at exponent `0`. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero :
    HasDerivAt
      Real.sinePowerGammaRatio
      (-Real.pi * Real.log 2)
      0 := by
  have hder :
      HasDerivAt
        Real.sinePowerGammaRatio
        (Real.pi *
          ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
        0 :=
    Real.sinePowerGammaRatio_hasDerivAt_zero_from_logDeriv
  exact
    Eq.subst
      (motive := fun d : ℝ => HasDerivAt Real.sinePowerGammaRatio d 0)
      Real.sinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two
      hder

/-- Near exponent `0`, the sine-power integral is represented by the
Beta/Gamma ratio. -/
theorem Real.sinePowerIntegral_eventuallyEq_gammaRatio_at_zero :
    (fun s : ℝ => Real.sinePowerIntegral s) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => Real.sinePowerGammaRatio s) := by
  have hnear :
      ∀ᶠ s in 𝓝 (0 : ℝ), -1 < s :=
    Ioi_mem_nhds (show -1 < (0 : ℝ) by exact neg_lt_zero.mpr one_pos)
  exact
    hnear.mono
      (fun s hs =>
        Real.sinePowerIntegral_eq_gammaRatio s hs)

/-- Transport the Gamma-ratio derivative to the sine-power integral using the
local Beta/Gamma identity near exponent `0`. -/
theorem Real.sinePowerIntegral_hasDerivAt_zero_from_gammaRatio :
    HasDerivAt
      Real.sinePowerIntegral
      (-Real.pi * Real.log 2)
      0 := by
  exact
    Real.sinePowerGammaRatio_hasDerivAt_zero.congr_of_eventuallyEq
      Real.sinePowerIntegral_eventuallyEq_gammaRatio_at_zero

/-- Derivative uniqueness identifies the two derivative values of the
sine-power integral at exponent `0`. -/
theorem Real.integral_log_sin_zero_pi_eq_gammaRatio_derivative :
    (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) =
      -Real.pi * Real.log 2 := by
  exact
    HasDerivAt.unique
      Real.sinePowerIntegral_hasDerivAt_zero
      Real.sinePowerIntegral_hasDerivAt_zero_from_gammaRatio

/-- The classical log-sine integral on `[0,π]`. -/
theorem Real.integral_log_sin_zero_pi :
    ∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u) =
      -Real.pi * Real.log 2 := by
  exact Real.integral_log_sin_zero_pi_eq_gammaRatio_derivative

end

end LFunctions
