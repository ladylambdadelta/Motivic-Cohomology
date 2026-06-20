import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.LogSineCircleKernel.SinePower.Owner

/-!
# Log-sine and unit-circle boundary kernel

This owner layer was split from `LogSineCircleKernel.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Elementary real algebra used in the unit-circle chord norm-square
calculation. -/
theorem real_one_sub_cos_sq_add_neg_sin_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 =
      2 * (1 - Real.cos θ) := by
  let c : ℝ := Real.cos θ
  let s : ℝ := Real.sin θ
  have hs_sq : s ^ 2 = 1 - c ^ 2 := by
    exact Real.sin_sq θ
  have hneg_sq : (-s) ^ 2 = s ^ 2 :=
    neg_sq s
  have hsub_sq : (1 - c) ^ 2 = 1 ^ 2 - 2 * 1 * c + c ^ 2 :=
    sub_sq 1 c
  have hone_sq : (1 : ℝ) ^ 2 = 1 :=
    one_pow 2
  have htwo_one_mul : 2 * (1 : ℝ) * c = 2 * c := by
    exact congrArg (fun x : ℝ => x * c) (mul_one 2)
  have hleft_expand :
      (1 - c) ^ 2 + (-s) ^ 2 =
        (1 - 2 * c + c ^ 2) + s ^ 2 := by
    calc
      (1 - c) ^ 2 + (-s) ^ 2 =
          (1 ^ 2 - 2 * 1 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => x + (-s) ^ 2) hsub_sq
      _ = (1 - 2 * 1 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => (x - 2 * 1 * c + c ^ 2) + (-s) ^ 2) hone_sq
      _ = (1 - 2 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => (1 - x + c ^ 2) + (-s) ^ 2) htwo_one_mul
      _ = (1 - 2 * c + c ^ 2) + s ^ 2 := by
        exact congrArg (fun x : ℝ => (1 - 2 * c + c ^ 2) + x) hneg_sq
  have hgroup :
      (1 - 2 * c + c ^ 2) + s ^ 2 =
        1 - 2 * c + (c ^ 2 + s ^ 2) := by
    calc
      (1 - 2 * c + c ^ 2) + s ^ 2 =
          ((1 - 2 * c) + c ^ 2) + s ^ 2 := by
        exact rfl
      _ = (1 - 2 * c) + (c ^ 2 + s ^ 2) := by
        exact add_assoc (1 - 2 * c) (c ^ 2) (s ^ 2)
      _ = 1 - 2 * c + (c ^ 2 + s ^ 2) := by
        exact rfl
  have hcos_sin : c ^ 2 + s ^ 2 = 1 := by
    exact Eq.trans (add_comm (c ^ 2) (s ^ 2)) (Real.sin_sq_add_cos_sq θ)
  have hcollapse :
      1 - 2 * c + (c ^ 2 + s ^ 2) = 1 - 2 * c + 1 := by
    exact congrArg (fun x : ℝ => 1 - 2 * c + x) hcos_sin
  have hfinal :
      1 - 2 * c + 1 = 2 * (1 - c) := by
    calc
      1 - 2 * c + 1 = (1 + 1) - 2 * c := by
        exact sub_add_eq_add_sub 1 (2 * c) 1
      _ = 2 - 2 * c := by
        exact congrArg (fun x : ℝ => x - 2 * c) (one_add_one_eq_two)
      _ = 2 * 1 - 2 * c := by
        exact congrArg (fun x : ℝ => x - 2 * c) (Eq.symm (mul_one 2))
      _ = 2 * (1 - c) := by
        exact (mul_sub 2 1 c).symm
  calc
    (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 =
        (1 - c) ^ 2 + (-s) ^ 2 := by
      exact rfl
    _ = (1 - 2 * c + c ^ 2) + s ^ 2 := by
      exact hleft_expand
    _ = 1 - 2 * c + (c ^ 2 + s ^ 2) := by
      exact hgroup
    _ = 1 - 2 * c + 1 := by
      exact hcollapse
    _ = 2 * (1 - c) := by
      exact hfinal
    _ = 2 * (1 - Real.cos θ) := by
      exact rfl

/-- Elementary real algebra used in the half-angle chord identity. -/
theorem real_two_abs_sin_half_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (2 * |Real.sin (θ / 2)|) ^ 2 =
      2 * (1 - Real.cos θ) := by
  let u : ℝ := θ / 2
  have habs_sq : |Real.sin u| ^ 2 = (Real.sin u) ^ 2 :=
    sq_abs (Real.sin u)
  have hmul_sq :
      (2 * |Real.sin u|) ^ 2 = 2 ^ 2 * |Real.sin u| ^ 2 :=
    mul_pow 2 |Real.sin u| 2
  have htwo_sq : (2 : ℝ) ^ 2 = 2 * 2 :=
    sq 2
  have hsin_half :
      (Real.sin u) ^ 2 = 1 / 2 - Real.cos (2 * u) / 2 :=
    Real.sin_sq_eq_half_sub u
  have htheta : 2 * u = θ := by
    calc
      2 * u = 2 * (θ / 2) := by
        exact rfl
      _ = 2 * θ / 2 := by
        exact mul_div_assoc' 2 θ 2
      _ = θ := by
        exact mul_div_cancel_left₀ θ two_ne_zero
  have hcos_theta :
      Real.cos (2 * u) = Real.cos θ :=
    congrArg Real.cos htheta
  have hfour_mul :
      (2 * 2) * (1 / 2 - Real.cos θ / 2) =
        2 * (1 - Real.cos θ) := by
    calc
      (2 * 2) * (1 / 2 - Real.cos θ / 2) =
          (2 * 2) * ((1 - Real.cos θ) / 2) := by
        exact
          congrArg (fun x : ℝ => (2 * 2) * x)
            (Eq.symm (sub_div 1 (Real.cos θ) 2))
      _ = 2 * (1 - Real.cos θ) := by
        have hinner :
            2 * ((1 - Real.cos θ) / 2) = 1 - Real.cos θ := by
          calc
            2 * ((1 - Real.cos θ) / 2) =
                2 * (1 - Real.cos θ) / 2 := by
              exact mul_div_assoc' 2 (1 - Real.cos θ) 2
            _ = 1 - Real.cos θ :=
              mul_div_cancel_left₀ (1 - Real.cos θ) two_ne_zero
        calc
          (2 * 2) * ((1 - Real.cos θ) / 2) =
              2 * (2 * ((1 - Real.cos θ) / 2)) :=
            mul_assoc 2 2 ((1 - Real.cos θ) / 2)
          _ = 2 * (1 - Real.cos θ) := by
            exact congrArg (fun x : ℝ => 2 * x) hinner
  calc
    (2 * |Real.sin (θ / 2)|) ^ 2 =
        (2 * |Real.sin u|) ^ 2 := by
      exact rfl
    _ = 2 ^ 2 * |Real.sin u| ^ 2 := by
      exact hmul_sq
    _ = (2 * 2) * |Real.sin u| ^ 2 := by
      exact congrArg (fun x : ℝ => x * |Real.sin u| ^ 2) htwo_sq
    _ = (2 * 2) * (Real.sin u) ^ 2 := by
      exact congrArg (fun x : ℝ => (2 * 2) * x) habs_sq
    _ = (2 * 2) * (1 / 2 - Real.cos (2 * u) / 2) := by
      exact congrArg (fun x : ℝ => (2 * 2) * x) hsin_half
    _ = (2 * 2) * (1 / 2 - Real.cos θ / 2) := by
      exact congrArg (fun x : ℝ => (2 * 2) * (1 / 2 - x / 2)) hcos_theta
    _ = 2 * (1 - Real.cos θ) := by
      exact hfour_mul

/-- Complex norm-square chord calculation on the unit circle. -/
theorem unitCircleLogKernel_normSq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      2 * (1 - Real.cos θ) := by
  have hexp :
      Complex.exp ((θ : ℂ) * Complex.I) =
        (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    calc
      Complex.exp ((θ : ℂ) * Complex.I) =
          Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I :=
        Complex.exp_mul_I θ
      _ = (Real.cos θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I := by
        exact congrArg
          (fun x : ℂ => x + Complex.sin (θ : ℂ) * Complex.I)
          (Complex.ofReal_cos θ).symm
      _ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
        exact congrArg
          (fun x : ℂ => (Real.cos θ : ℂ) + x * Complex.I)
          (Complex.ofReal_sin θ).symm
  have hnorm :
      Complex.normSq (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) =
        (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 := by
    have hsub_complex :
        1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) =
          ((1 - Real.cos θ : ℝ) : ℂ) + ((-Real.sin θ : ℝ) : ℂ) * Complex.I := by
      have hsinI_re :
          ((Real.sin θ : ℂ) * Complex.I).re = 0 := by
        calc
          ((Real.sin θ : ℂ) * Complex.I).re =
              Real.sin θ * 0 - 0 * 1 := by
            exact rfl
          _ = Real.sin θ * 0 - 0 := by
            exact congrArg (fun x : ℝ => Real.sin θ * 0 - x) (zero_mul 1)
          _ = 0 - 0 := by
            exact congrArg (fun x : ℝ => x - 0) (mul_zero (Real.sin θ))
          _ = 0 := sub_self 0
      have hsinI_im :
          ((Real.sin θ : ℂ) * Complex.I).im = Real.sin θ := by
        calc
          ((Real.sin θ : ℂ) * Complex.I).im =
              Real.sin θ * 1 + 0 * 0 := by
            exact rfl
          _ = Real.sin θ + 0 * 0 := by
            exact congrArg (fun x : ℝ => x + 0 * 0) (mul_one (Real.sin θ))
          _ = Real.sin θ + 0 := by
            exact congrArg (fun x : ℝ => Real.sin θ + x) (zero_mul 0)
          _ = Real.sin θ := add_zero (Real.sin θ)
      have hnegSinI_re :
          (((-Real.sin θ : ℝ) : ℂ) * Complex.I).re = 0 := by
        calc
          (((-Real.sin θ : ℝ) : ℂ) * Complex.I).re =
              (-Real.sin θ) * 0 - 0 * 1 := by
            exact rfl
          _ = (-Real.sin θ) * 0 - 0 := by
            exact congrArg (fun x : ℝ => (-Real.sin θ) * 0 - x) (zero_mul 1)
          _ = 0 - 0 := by
            exact congrArg (fun x : ℝ => x - 0) (mul_zero (-Real.sin θ))
          _ = 0 := sub_self 0
      have hnegSinI_im :
          (((-Real.sin θ : ℝ) : ℂ) * Complex.I).im = -Real.sin θ := by
        calc
          (((-Real.sin θ : ℝ) : ℂ) * Complex.I).im =
              (-Real.sin θ) * 1 + 0 * 0 := by
            exact rfl
          _ = -Real.sin θ + 0 * 0 := by
            exact congrArg (fun x : ℝ => x + 0 * 0) (mul_one (-Real.sin θ))
          _ = -Real.sin θ + 0 := by
            exact congrArg (fun x : ℝ => -Real.sin θ + x) (zero_mul 0)
          _ = -Real.sin θ := add_zero (-Real.sin θ)
      have hre_lhs :
          (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)).re =
            1 - Real.cos θ := by
        calc
          (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)).re =
              1 - (Real.cos θ + ((Real.sin θ : ℂ) * Complex.I).re) := by
            exact rfl
          _ = 1 - (Real.cos θ + 0) := by
            exact congrArg (fun x : ℝ => 1 - (Real.cos θ + x)) hsinI_re
          _ = 1 - Real.cos θ := by
            exact congrArg (fun x : ℝ => 1 - x) (add_zero (Real.cos θ))
      have hre_rhs :
          (((1 - Real.cos θ : ℝ) : ℂ) + ((-Real.sin θ : ℝ) : ℂ) * Complex.I).re =
            1 - Real.cos θ := by
        calc
          (((1 - Real.cos θ : ℝ) : ℂ) + ((-Real.sin θ : ℝ) : ℂ) * Complex.I).re =
              (1 - Real.cos θ) + (((-Real.sin θ : ℝ) : ℂ) * Complex.I).re := by
            exact rfl
          _ = (1 - Real.cos θ) + 0 := by
            exact congrArg (fun x : ℝ => (1 - Real.cos θ) + x) hnegSinI_re
          _ = 1 - Real.cos θ := add_zero (1 - Real.cos θ)
      have him_lhs :
          (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)).im =
            -Real.sin θ := by
        calc
          (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)).im =
              0 - (0 + ((Real.sin θ : ℂ) * Complex.I).im) := by
            exact rfl
          _ = 0 - (0 + Real.sin θ) := by
            exact congrArg (fun x : ℝ => 0 - (0 + x)) hsinI_im
          _ = 0 - Real.sin θ := by
            exact congrArg (fun x : ℝ => 0 - x) (zero_add (Real.sin θ))
          _ = -Real.sin θ := zero_sub (Real.sin θ)
      have him_rhs :
          (((1 - Real.cos θ : ℝ) : ℂ) + ((-Real.sin θ : ℝ) : ℂ) * Complex.I).im =
            -Real.sin θ := by
        calc
          (((1 - Real.cos θ : ℝ) : ℂ) + ((-Real.sin θ : ℝ) : ℂ) * Complex.I).im =
              0 + (((-Real.sin θ : ℝ) : ℂ) * Complex.I).im := by
            exact rfl
          _ = 0 + -Real.sin θ := by
            exact congrArg (fun x : ℝ => 0 + x) hnegSinI_im
          _ = -Real.sin θ := zero_add (-Real.sin θ)
      exact Complex.ext (hre_lhs.trans hre_rhs.symm) (him_lhs.trans him_rhs.symm)
    calc
      Complex.normSq (1 - ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I)) =
          Complex.normSq ((1 - Real.cos θ : ℝ) + (-Real.sin θ : ℝ) * Complex.I) := by
        exact congrArg Complex.normSq hsub_complex
      _ = (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 :=
        Complex.normSq_add_mul_I (1 - Real.cos θ) (-Real.sin θ)
  calc
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
        Complex.normSq (1 - (Real.cos θ + Real.sin θ * Complex.I)) := by
      exact congrArg (fun z : ℂ => Complex.normSq (1 - z)) hexp
    _ = (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 := by
      exact hnorm
    _ = 2 * (1 - Real.cos θ) := by
      exact real_one_sub_cos_sq_add_neg_sin_sq_eq_two_mul_one_sub_cos θ

/-- Half-angle square identity for the unit-circle chord length. -/
theorem unitCircleLogKernel_two_abs_sin_half_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (2 * |Real.sin (θ / 2)|) ^ 2 =
      2 * (1 - Real.cos θ) := by
  exact real_two_abs_sin_half_sq_eq_two_mul_one_sub_cos θ

/-- Squared chord length for the unit-circle logarithmic kernel.

This is the coordinate norm-square calculation:
`|1 - e^{iθ}|² = (2 |sin(θ/2)|)²`. -/
theorem unitCircleLogKernel_norm_sq_eq_two_abs_sin_half_sq
    (θ : ℝ) :
    ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
  let z : ℂ := 1 - Complex.exp (θ * Complex.I)
  calc
    ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 =
        Complex.abs z ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) (Complex.norm_eq_abs z)
    _ = Complex.normSq z := by
      exact Complex.sq_abs z
    _ = 2 * (1 - Real.cos θ) := by
      exact unitCircleLogKernel_normSq_eq_two_mul_one_sub_cos θ
    _ = (2 * |Real.sin (θ / 2)|) ^ 2 := by
      exact (unitCircleLogKernel_two_abs_sin_half_sq_eq_two_mul_one_sub_cos θ).symm

/-- Unit-circle kernel norm as the sine half-angle expression. -/
theorem unitCircleLogKernel_norm_eq_two_abs_sin_half
    (θ : ℝ) :
    ‖1 - Complex.exp (θ * Complex.I)‖ =
      2 * |Real.sin (θ / 2)| := by
  have hleft_nonneg :
      0 ≤ ‖1 - Complex.exp (θ * Complex.I)‖ :=
    norm_nonneg (1 - Complex.exp (θ * Complex.I))
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hright_nonneg :
      0 ≤ 2 * |Real.sin (θ / 2)| :=
    mul_nonneg htwo_nonneg (abs_nonneg (Real.sin (θ / 2)))
  exact
    (sq_eq_sq₀ hleft_nonneg hright_nonneg).1
      (unitCircleLogKernel_norm_sq_eq_two_abs_sin_half_sq θ)

/-- Pointwise logarithmic split of the unit-circle kernel away from the
finite endpoint singularities. -/
theorem unitCircleLogKernel_log_eq_const_plus_halfSineLog_of_sin_ne_zero
    (θ : ℝ)
    (hθ : Real.sin (θ / 2) ≠ 0) :
    Real.log ‖1 - Complex.exp (θ * Complex.I)‖ =
      Real.log 2 + Real.log |Real.sin (θ / 2)| := by
  have hnorm :
      ‖1 - Complex.exp (θ * Complex.I)‖ =
        2 * |Real.sin (θ / 2)| :=
    unitCircleLogKernel_norm_eq_two_abs_sin_half θ
  have htwo : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have habs : |Real.sin (θ / 2)| ≠ 0 :=
    abs_ne_zero.mpr hθ
  calc
    Real.log ‖1 - Complex.exp (θ * Complex.I)‖ =
        Real.log (2 * |Real.sin (θ / 2)|) := by
      exact congrArg Real.log hnorm
    _ = Real.log 2 + Real.log |Real.sin (θ / 2)| := by
      exact Real.log_mul htwo habs

/-- The endpoint singularity set of the half-angle unit-circle kernel is null
on the fundamental Jensen interval. -/
theorem unitCircleLogKernel_halfSine_zero_ae_ne :
    ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
      Real.sin (θ / 2) ≠ 0 := by
  have hne_endpoint :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ≠ 2 * Real.pi :=
    MeasureTheory.ae_restrict_of_ae
      ((Set.countable_singleton (2 * Real.pi)).ae_not_mem MeasureTheory.volume)
  have hinterval :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) :=
    MeasureTheory.ae_restrict_mem measurableSet_uIoc
  exact
    (hne_endpoint.and hinterval).mono
      (fun θ hθ =>
        have hθ_ne_endpoint : θ ≠ 2 * Real.pi := hθ.1
        have hθ_interval : θ ∈ Ι (0 : ℝ) (2 * Real.pi) := hθ.2
        have hθ_cases :
            0 < θ ∧ θ ≤ 2 * Real.pi ∨ 2 * Real.pi < θ ∧ θ ≤ 0 :=
          Set.mem_uIoc.1 hθ_interval
        match hθ_cases with
        | Or.inl hmain =>
            have hθ_lt_endpoint : θ < 2 * Real.pi :=
              lt_of_le_of_ne hmain.2 hθ_ne_endpoint
            have hhalf_pos : 0 < θ / 2 :=
              div_pos hmain.1 zero_lt_two
            have hhalf_lt_pi : θ / 2 < Real.pi := by
              have hθ_lt_pi_mul_two : θ < Real.pi * 2 :=
                lt_of_lt_of_eq hθ_lt_endpoint (mul_comm 2 Real.pi)
              exact (div_lt_iff₀ zero_lt_two).2 hθ_lt_pi_mul_two
            (Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt_pi).ne'
        | Or.inr hrev =>
            have hendpoint_le_zero : 2 * Real.pi ≤ 0 :=
              hrev.1.le.trans hrev.2
            have hendpoint_pos : 0 < 2 * Real.pi :=
              mul_pos zero_lt_two Real.pi_pos
            False.elim ((not_lt_of_ge hendpoint_le_zero) hendpoint_pos))

/-- Restricted-a.e. logarithmic split of the unit-circle kernel on the
fundamental interval.

The exceptional set is the finite set of endpoint singularities where
`sin (θ/2) = 0`. -/
theorem unitCircleLogKernel_log_eq_const_plus_halfSineLog_ae :
    (fun θ : ℝ => Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =ᵐ[
        MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
      (fun θ : ℝ => Real.log 2 + Real.log |Real.sin (θ / 2)|) := by
  exact
    unitCircleLogKernel_halfSine_zero_ae_ne.mono
      (fun θ hθ =>
        unitCircleLogKernel_log_eq_const_plus_halfSineLog_of_sin_ne_zero θ hθ)

/-- Integral split after the pointwise half-angle norm identity. -/
theorem unitCircleLogKernel_integral_eq_const_plus_halfSineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log 2 + Real.log |Real.sin (θ / 2)| := by
  exact
    intervalIntegral.integral_congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).1
        unitCircleLogKernel_log_eq_const_plus_halfSineLog_ae)


end
end LFunctions
end Boundary
