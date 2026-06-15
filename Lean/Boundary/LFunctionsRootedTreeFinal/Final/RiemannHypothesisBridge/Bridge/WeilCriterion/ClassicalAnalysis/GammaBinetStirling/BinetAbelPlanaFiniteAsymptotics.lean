import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaCore
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Finite asymptotic owners for the Abel-Plana proof of Binet's formula

This file owns the two standard analytic estimates behind the finite
Abel-Plana limit passage:

* the endpoint logarithmic Stirling remainder tends to zero;
* the finite Abel-Plana contour remainder has norm tending to zero.

The downstream classical-input file should only assemble these estimates with
the concrete finite terms from `BinetAbelPlanaCore`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The factorial part of the logarithmic Stirling endpoint error. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℂ :=
  Complex.log ((Nat.factorial M : ℕ) : ℂ) -
    (((M : ℂ) + (1 / 2 : ℂ)) * Complex.log (M : ℂ) -
      (M : ℂ) +
        (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2)

/-- Real-valued factorial Stirling endpoint error before coercion to `ℂ`. -/
noncomputable def Real.binetAbelPlanaFactorialStirlingError
    (M : ℕ) : ℝ :=
  Real.log ((Nat.factorial M : ℕ) : ℝ) -
    (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
      (M : ℝ) +
        Real.log (2 * Real.pi) / 2)

/-- The real factorial Stirling endpoint error is the logarithm of mathlib's
Stirling sequence, normalized by its limiting value `√π`. -/
theorem Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
    (M : ℕ)
    (hM : M ≠ 0) :
    Real.binetAbelPlanaFactorialStirlingError M =
      Real.log (Stirling.stirlingSeq M) - Real.log (Real.sqrt Real.pi) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have htwoMpos : 0 < (2 : ℝ) * M := mul_pos two_pos hMpos_real
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsqrt_pi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
  have hlog_sqrt_pi :
      Real.log (Real.sqrt Real.pi) = Real.log Real.pi / 2 := by
    exact Real.log_sqrt hpi_pos.le
  have hlog_two_mul_M :
      Real.log ((2 : ℝ) * M) = Real.log (2 : ℝ) + Real.log (M : ℝ) := by
    exact Real.log_mul two_ne_zero hMpos_real.ne'
  have hlog_M_div_exp :
      Real.log ((M : ℝ) / Real.exp 1) = Real.log (M : ℝ) - 1 := by
    have hdiv : Real.log ((M : ℝ) / Real.exp 1) =
        Real.log (M : ℝ) - Real.log (Real.exp 1) :=
      Real.log_div hMpos_real.ne' (Real.exp_pos 1).ne'
    have hlog_exp : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    linarith
  have hlog_two_pi :
      Real.log (2 * Real.pi) = Real.log (2 : ℝ) + Real.log Real.pi := by
    exact Real.log_mul two_ne_zero hpi_pos.ne'
  calc
    Real.binetAbelPlanaFactorialStirlingError M
        =
        Real.log ((Nat.factorial M : ℕ) : ℝ) -
          (((M : ℝ) + (1 / 2 : ℝ)) * Real.log (M : ℝ) -
            (M : ℝ) +
              Real.log (2 * Real.pi) / 2) := by
          rfl
    _ =
        (Real.log ((Nat.factorial M : ℕ) : ℝ) -
            (1 / 2 : ℝ) * Real.log ((2 : ℝ) * M) -
              (M : ℝ) * Real.log ((M : ℝ) / Real.exp 1)) -
          Real.log (Real.sqrt Real.pi) := by
          have h1 := hlog_sqrt_pi
          have h2 := hlog_two_mul_M
          have h3 := hlog_M_div_exp
          have h4 := hlog_two_pi
          linarith
    _ =
        Real.log (Stirling.stirlingSeq M) -
          Real.log (Real.sqrt Real.pi) := by
          exact Stirling.log_stirlingSeq_formula M

/-- The complex factorial Stirling endpoint error is the coercion of its real
normal form. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
    (M : ℕ)
    (hM : M ≠ 0) :
    Complex.binetAbelPlanaFactorialStirlingError M =
      (Real.binetAbelPlanaFactorialStirlingError M : ℂ) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hfact_nonneg :
      0 ≤ ((Nat.factorial M : ℕ) : ℝ) :=
    Nat.cast_nonneg (Nat.factorial M)
  have hM_nonneg : 0 ≤ (M : ℝ) := hMpos_real.le
  have htwo_pi_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
    (mul_pos two_pos Real.pi_pos).le
  dsimp [Complex.binetAbelPlanaFactorialStirlingError,
    Real.binetAbelPlanaFactorialStirlingError]
  norm_num [Complex.ofReal_log, hfact_nonneg, hM_nonneg, htwo_pi_nonneg]

/-- The real factorial Stirling endpoint error tends to zero. -/
theorem Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Tendsto
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hstirling :
      Tendsto
        (fun N : ℕ => Stirling.stirlingSeq (N + 1))
        atTop
        (𝓝 (Real.sqrt Real.pi)) :=
    Stirling.tendsto_stirlingSeq_sqrt_pi.comp
      (tendsto_add_atTop_nat 1)
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 :=
    (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hlog :
      Tendsto
        (fun N : ℕ => Real.log (Stirling.stirlingSeq (N + 1)))
        atTop
        (𝓝 (Real.log (Real.sqrt Real.pi))) :=
    (Real.continuousAt_log hsqrt_ne).tendsto.comp hstirling
  have hsub :
      Tendsto
        (fun N : ℕ =>
          Real.log (Stirling.stirlingSeq (N + 1)) -
            Real.log (Real.sqrt Real.pi))
        atTop
        (𝓝 (Real.log (Real.sqrt Real.pi) -
          Real.log (Real.sqrt Real.pi))) :=
    hlog.sub tendsto_const_nhds
  have heq :
      (fun N : ℕ =>
        Real.binetAbelPlanaFactorialStirlingError (N + 1)) =
      (fun N : ℕ =>
        Real.log (Stirling.stirlingSeq (N + 1)) -
          Real.log (Real.sqrt Real.pi)) := by
    funext N
    exact
      Real.binetAbelPlanaFactorialStirlingError_eq_log_stirlingSeq_sub_log_sqrt_pi
        (N + 1)
        (Nat.succ_ne_zero N)
  exact sub_self (Real.log (Real.sqrt Real.pi)) ▸ (heq ▸ hsub)

/-- The endpoint shift error measuring
`(M + w + 1/2) log (1 + w/M) - w`, in branch-safe difference form. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  ((w + (M : ℂ) + (1 / 2 : ℂ)) *
      (Complex.log (M : ℂ) - Complex.log (w + (M : ℂ)))) +
    w

/-- The positive-real scaling factor in the endpoint logarithm. -/
noncomputable def Complex.binetEndpointScale
    (M : ℕ) : ℂ :=
  (M : ℂ)

/-- The small logarithmic endpoint variable `w / M`. -/
noncomputable def Complex.binetEndpointSmallVariable
    (w : ℂ)
    (M : ℕ) : ℂ :=
  w / Complex.binetEndpointScale M

/-- The endpoint logarithmic Taylor error `log (1 + z) - z`. -/
noncomputable def Complex.binetEndpointLogTaylorError
    (w : ℂ)
    (M : ℕ) : ℂ :=
  Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
    Complex.binetEndpointSmallVariable w M

/-- The endpoint logarithmic branch identity in the open right half-plane. -/
theorem Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.log (w + (M : ℂ)) =
      Complex.log (M : ℂ) +
        Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hsmall_ne :
      (1 + Complex.binetEndpointSmallVariable w M) ≠ 0 := by
    intro hzero
    have hre :
        (1 + Complex.binetEndpointSmallVariable w M).re = 0 := by
      exact congrArg Complex.re hzero
    have hre_pos :
        0 < (1 + Complex.binetEndpointSmallVariable w M).re := by
      dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
      norm_num [Complex.add_re, Complex.one_re, Complex.div_re,
        Complex.ofNat_re, Complex.ofNat_im, hMpos_real.ne']
      exact add_pos_of_pos_of_nonneg zero_lt_one
        (div_nonneg hw.le hMpos_real.le)
    exact (ne_of_gt hre_pos) hre
  have hprod :
      ((M : ℂ) *
          (1 + Complex.binetEndpointSmallVariable w M)) =
        w + (M : ℂ) := by
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    field_simp [show (M : ℂ) ≠ 0 by exact_mod_cast hM]
    ring
  calc
    Complex.log (w + (M : ℂ))
        = Complex.log ((M : ℂ) *
            (1 + Complex.binetEndpointSmallVariable w M)) := by
          exact congrArg Complex.log hprod
    _ = Real.log (M : ℝ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
          exact
            Complex.log_ofReal_mul hMpos_real hsmall_ne
    _ = Complex.log (M : ℂ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) := by
          exact (Complex.ofReal_log hMpos_real.le).symm

/-- Branch-safe endpoint log-shift error in Taylor-remainder normal form. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re) :
    Complex.binetAbelPlanaEndpointLogShiftError w M =
      -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M := by
  have hlog :
      Complex.log (w + (M : ℂ)) =
        Complex.log (M : ℂ) +
          Complex.log (1 + Complex.binetEndpointSmallVariable w M) :=
    Complex.binetEndpoint_log_nat_add_eq_log_nat_add_log_one_add hM hw
  have hM_ne : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM
  dsimp [Complex.binetAbelPlanaEndpointLogShiftError,
    Complex.binetEndpointLogTaylorError,
    Complex.binetEndpointSmallVariable,
    Complex.binetEndpointScale]
  exact congrArg (fun z : ℂ =>
    z -
      Complex.binetEndpointSmallVariable w M) hlog
  field_simp [hM_ne]
  ring

/-- Eventually the endpoint small variable lies in the Taylor disk
`‖z‖ ≤ 1 / 2`. -/
theorem Complex.eventually_norm_binetEndpointSmallVariable_le_half
    (w : ℂ) :
    ∀ᶠ M : ℕ in atTop,
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
  have hbound :
      ∀ᶠ M : ℕ in atTop, 2 * ‖w‖ ≤ (M : ℝ) := by
    exact eventually_ge_atTop (Nat.ceil (2 * ‖w‖))
  filter_upwards [hbound] with M hM
  by_cases hMzero : M = 0
  · subst M
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    exact le_of_eq (by norm_num)
  · have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hMzero
    have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    exact
      (div_le_iff₀ hMpos_real).mpr
        (by
          have : (M : ℝ) ≤ 2 * ‖w‖ := by linarith
          exact this)
    exact hM

/-- Taylor bound for the endpoint logarithmic error in the eventual small
variable range. -/
theorem Complex.norm_binetEndpointLogTaylorError_le_square
    {w : ℂ}
    {M : ℕ}
    (hsmall :
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.binetEndpointLogTaylorError w M‖ ≤
      ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 := by
  have hlt :
      ‖Complex.binetEndpointSmallVariable w M‖ < 1 :=
    lt_of_le_of_lt hsmall one_half_lt_one
  have hraw :
      ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
          Complex.binetEndpointSmallVariable w M‖ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 *
          (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ / 2 :=
    Complex.norm_log_one_add_sub_self_le hlt
  have hden :
      (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ ≤ (2 : ℝ) := by
    have hpos : 0 < 1 - ‖Complex.binetEndpointSmallVariable w M‖ := by
      linarith
    have hhalf : (1 / 2 : ℝ) ≤ 1 - ‖Complex.binetEndpointSmallVariable w M‖ := by
      linarith
    have hpos2 : 0 < (2 : ℝ) := by positivity
    have hinv := (inv_le_comm₀ hpos hpos2).2 hhalf
    linarith
  dsimp [Complex.binetEndpointLogTaylorError]
  calc
    ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
        Complex.binetEndpointSmallVariable w M‖
        ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 *
          (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ / 2 := hraw
    _ ≤ ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 * 2 / 2 := by
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hden
            (sq_nonneg ‖Complex.binetEndpointSmallVariable w M‖))
          zero_le_two
    _ = ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 := by
      ring

/-- Large-endpoint bound for the branch-safe logarithmic shift error. -/
theorem Complex.norm_binetAbelPlanaEndpointLogShiftError_le_large_endpoint_majorant
    {w : ℂ}
    {M : ℕ}
    (hM : M ≠ 0)
    (hw : 0 < w.re)
    (hlarge : 2 * (1 + ‖w‖) ≤ (M : ℝ)) :
    ‖Complex.binetAbelPlanaEndpointLogShiftError w M‖ ≤
      4 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
  have hMpos_nat : 0 < M := Nat.pos_of_ne_zero hM
  have hMpos_real : 0 < (M : ℝ) := Nat.cast_pos.mpr hMpos_nat
  have hM_complex_ne : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM
  have hsmall :
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    norm_num [norm_div, Complex.norm_natCast]
    have hhalf : ‖w‖ ≤ (1 / 2 : ℝ) * (M : ℝ) := by
      nlinarith [norm_nonneg w, hlarge]
    exact hhalf
  have htaylor :
      ‖Complex.binetEndpointLogTaylorError w M‖ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 :=
    Complex.norm_binetEndpointLogTaylorError_le_square hsmall
  have hsmall_norm :
      ‖Complex.binetEndpointSmallVariable w M‖ =
        ‖w‖ / (M : ℝ) := by
    dsimp [Complex.binetEndpointSmallVariable, Complex.binetEndpointScale]
    norm_num [norm_div, Complex.norm_natCast]
  have hnormal :
      Complex.binetAbelPlanaEndpointLogShiftError w M =
        -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
          (w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M :=
    Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form hM hw
  have hfirst :
      ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) := by
    norm_num [norm_div, Complex.norm_natCast]
    have hnum :
        ‖w * (w + (1 / 2 : ℂ))‖ ≤ (1 + ‖w‖) ^ 2 := by
      calc
        ‖w * (w + (1 / 2 : ℂ))‖
            = ‖w‖ * ‖w + (1 / 2 : ℂ)‖ := norm_mul _ _
        _ ≤ ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg w)
        _ ≤ (1 + ‖w‖) ^ 2 := by
          have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
            norm_num
          norm_num [hhalf_norm]
          nlinarith [norm_nonneg w]
    exact div_le_div_of_nonneg_right hnum hMpos_real.le
  have hsecond :
      ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖ ≤
        3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
    norm_num [norm_mul]
    have hendpoint :
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ ≤
          (3 / 2 : ℝ) * (M : ℝ) := by
      calc
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖
            ≤ ‖w‖ + ‖(M : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
              exact (norm_add_le (w + (M : ℂ)) (1 / 2 : ℂ)).trans
                (add_le_add_right (norm_add_le w (M : ℂ)) ‖(1 / 2 : ℂ)‖)
        _ = ‖w‖ + (M : ℝ) + (1 / 2 : ℝ) := by
              norm_num [Complex.norm_natCast]
        _ ≤ (3 / 2 : ℝ) * (M : ℝ) := by
              nlinarith [norm_nonneg w, hlarge, hMpos_real]
    have htailor_bound :
        ‖Complex.binetEndpointLogTaylorError w M‖ ≤
          (‖w‖ / (M : ℝ)) ^ 2 := by
      exact hsmall_norm.symm ▸ htaylor
    calc
      ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ *
          ‖Complex.binetEndpointLogTaylorError w M‖
          ≤
          ((3 / 2 : ℝ) * (M : ℝ)) *
            ((‖w‖ / (M : ℝ)) ^ 2) := by
            exact mul_le_mul hendpoint htailor_bound
              (norm_nonneg _) (by positivity)
      _ ≤ 3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
            have hMpos : 0 < (M : ℝ) := hMpos_real
            have hr_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
            field_simp [hMpos.ne']
            nlinarith [sq_nonneg ‖w‖, hr_nonneg]
  exact hnormal ▸ by
  calc
    ‖-((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
        (w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖
        ≤
      ‖((w * (w + (1 / 2 : ℂ))) / (M : ℂ))‖ +
          ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M‖ := by
          norm_num [sub_eq_add_neg, norm_neg, add_comm, add_left_comm,
            add_assoc]
    _ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) +
          3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          exact add_le_add hfirst hsecond
    _ ≤ 4 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          have hMpos : 0 < (M : ℝ) := hMpos_real
          have hone : 1 ≤ 1 + ‖w‖ := by
            exact le_add_of_nonneg_right (norm_nonneg w)
          have hsquare_le_cube :
              (1 + ‖w‖) ^ 2 ≤ (1 + ‖w‖) ^ 3 := by
            nlinarith [hone, sq_nonneg (1 + ‖w‖)]
          exact
            (add_le_add_right
              (div_le_div_of_nonneg_right hsquare_le_cube hMpos.le)
              (3 * (1 + ‖w‖) ^ 3 / (M : ℝ))).trans
              (by ring_nf)

/-- Exact algebraic endpoint decomposition: the finite endpoint remainder is
the sum of the factorial Stirling error and the branch-safe endpoint shift
error. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w =
      Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1) := by
  dsimp [Complex.binetAbelPlanaFiniteEndpointStirlingRemainder,
    Complex.binetAbelPlanaFiniteMainTerm,
    Complex.binetLogGammaMainTerm,
    Complex.binetAbelPlanaFactorialStirlingError,
    Complex.binetAbelPlanaEndpointLogShiftError]
  ring

/-- Factorial Stirling error majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingMajorant
    (N : ℕ) : ℝ :=
  (1 : ℝ) / (N + 1 : ℝ)

/-- Endpoint logarithmic-shift majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  4 * (1 + ‖w‖) ^ 3 / (N + 1 : ℝ)

/-- Explicit endpoint-Stirling majorant for the finite Abel-Plana endpoint
remainder.

The intended classical proof gives a branch-coherent logarithmic Stirling
expansion with an `O(1 / N)` endpoint error after replacing
`log (N + 1 + w)` by `log (N + 1) + log (1 + w / (N + 1))`. -/
noncomputable def Complex.binetAbelPlanaEndpointStirlingMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  Complex.binetAbelPlanaFactorialStirlingMajorant N +
    Complex.binetAbelPlanaEndpointLogShiftMajorant w N

/-- The factorial Stirling majorant tends to zero. -/
theorem Complex.binetAbelPlanaFactorialStirlingMajorant_tendsto_zero :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N) =
      (fun N : ℕ => ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaFactorialStirlingMajorant]
    exact one_div (N + 1 : ℝ)
  exact heq ▸ hinv

/-- The endpoint logarithmic-shift majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Tendsto
        (fun _N : ℕ => 4 * (1 + ‖w‖) ^ 3)
        atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3)) :=
    tendsto_const_nhds
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Tendsto
        (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3 * 0)) :=
    hconst.mul hinv
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N) =
      (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaEndpointLogShiftMajorant]
    ring_nf
  exact (mul_zero (4 * (1 + ‖w‖) ^ 3)).symm ▸ (heq ▸ hmul)

/-- The endpoint-Stirling majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointStirlingMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFactorialStirlingMajorant_tendsto_zero
  have hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N +
            Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hfactorial.add hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N +
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N) := by
    funext N
    rfl
  exact (zero_add (0 : ℝ)).symm ▸ (heq ▸ hsum)

/-- The factorial Stirling component tends to zero by mathlib's Stirling
formula. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1))
      atTop
      (𝓝 (0 : ℂ)) := by
  have hreal :
      Tendsto
        (fun N : ℕ =>
          Real.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℝ)) :=
    Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hcomplex :
      Tendsto
        (fun N : ℕ =>
          (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ))
        atTop
        (𝓝 ((0 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.tendsto 0 |>.comp hreal
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1)) =
      (fun N : ℕ =>
        (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ)) := by
    funext N
    exact
      Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
        (N + 1)
        (Nat.succ_ne_zero N)
  exact heq ▸ hcomplex

/-- Owner logarithmic-shift estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N := by
  have hlarge :
      ∀ᶠ N : ℕ in atTop,
        2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) := by
    refine eventually_atTop.mpr ?_
    refine ⟨Nat.ceil (2 * (1 + ‖w‖)), ?_⟩
    intro N hN
    have hceil :
        2 * (1 + ‖w‖) ≤ ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) :=
      Nat.le_ceil (2 * (1 + ‖w‖))
    have hNreal :
        ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) ≤ (N : ℝ) :=
      Nat.cast_le.mpr hN
    have hN_le_succ : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ N
    exact hceil.trans (hNreal.trans hN_le_succ)
  filter_upwards [hlarge] with N hNlarge
  have hM_ne : N + 1 ≠ 0 := Nat.succ_ne_zero N
  have hlarge_M :
      2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) :=
    hNlarge
  have hraw :
      ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
        4 * (1 + ‖w‖) ^ 3 / ((N + 1 : ℕ) : ℝ) :=
    Complex.norm_binetAbelPlanaEndpointLogShiftError_le_large_endpoint_majorant
      hM_ne hw hlarge_M
  dsimp [Complex.binetAbelPlanaEndpointLogShiftMajorant]
  exact hraw

/-- The endpoint logarithmic-shift component tends to zero from its explicit
majorant. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
      atTop
      (𝓝 (0 : ℂ)) := by
  have hbound :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N :=
    Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner hw
  have hmajorant :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖)
        atTop
        (𝓝 (0 : ℝ)) :=
    squeeze_zero'
      (Eventually.of_forall
        (fun N : ℕ =>
          norm_nonneg
            (Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))))
      hbound
      hmajorant
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Endpoint-Stirling remainder convergence assembled from the factorial
Stirling convergence and the endpoint logarithmic-shift convergence. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_from_components
    {w : ℂ}
    (hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℂ)))
    (hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
            Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 ((0 : ℂ) + 0)) :=
    hfactorial.add hshift
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)) := by
    funext N
    exact
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
        w N
  exact (zero_add (0 : ℂ)).symm ▸ (heq ▸ hsum)

/-- Endpoint logarithmic Stirling remainder for the finite Abel-Plana main
term.

This is the classical branch-compatible finite endpoint estimate: after the
Euler-product endpoint terms are put in the principal-log normalization used
by `binetLogGammaMainTerm`, their difference from the limiting Binet main term
vanishes.  See the standard Binet derivation in Whittaker-Watson, Ch. XII, or
DLMF §5.11.3. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hfactorial :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hshift :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlanaEndpointLogShiftError_tendsto_zero_owner hw
  exact
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_from_components
      hfactorial hshift

/-- Algebraic assembly of finite-main-term convergence from the endpoint
Stirling remainder estimate. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_of_endpointStirlingRemainder
    {w : ℂ}
    (hendpoint :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
        atTop
        (𝓝 (0 : ℂ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
            Complex.binetLogGammaMainTerm w)
        atTop
        (𝓝 (0 + Complex.binetLogGammaMainTerm w)) :=
    hendpoint.add tendsto_const_nhds
  have hfinite_eq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
          Complex.binetLogGammaMainTerm w) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w) := by
    funext N
    calc
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
          Complex.binetLogGammaMainTerm w
          =
          (Complex.binetAbelPlanaFiniteMainTerm N w -
              Complex.binetLogGammaMainTerm w) +
            Complex.binetLogGammaMainTerm w := by
        rfl
      _ = Complex.binetAbelPlanaFiniteMainTerm N w := by
        exact sub_add_cancel
          (Complex.binetAbelPlanaFiniteMainTerm N w)
          (Complex.binetLogGammaMainTerm w)
  have htarget :
      (0 : ℂ) + Complex.binetLogGammaMainTerm w =
        Complex.binetLogGammaMainTerm w :=
    zero_add (Complex.binetLogGammaMainTerm w)
  exact htarget ▸ (hfinite_eq ▸ hsum)

/-- Finite endpoint/Stirling asymptotic in the concrete finite-main-term
form. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_from_endpointStirling_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  exact
    Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_of_endpointStirlingRemainder
      (Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_owner
        hw)

/-- The scalar exponential kernel controlling the upper vertical Abel-Plana
residual. -/
noncomputable def Complex.binetAbelPlanaVerticalKernelMajorant
    (t : ℝ) : ℝ :=
  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- The finite mass of the Abel-Plana vertical kernel. -/
noncomputable def Complex.binetAbelPlanaVerticalKernelMass : ℝ :=
  ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.binetAbelPlanaVerticalKernelMajorant t

/-- The Abel-Plana vertical kernel is the existing Binet real majorant. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_eq_binetMajorant
    (t : ℝ) :
    Complex.binetAbelPlanaVerticalKernelMajorant t =
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  rfl

/-- The Abel-Plana vertical kernel is nonnegative on the positive half-line. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        0 ≤ Complex.binetAbelPlanaVerticalKernelMajorant t := by
  intro t ht
  dsimp [Complex.binetAbelPlanaVerticalKernelMajorant]
  exact Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht

/-- The Abel-Plana vertical kernel is integrable on the positive half-line. -/
theorem Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn :
    IntegrableOn
      (fun t : ℝ => Complex.binetAbelPlanaVerticalKernelMajorant t)
      (Set.Ioi (0 : ℝ)) := by
  dsimp [Complex.binetAbelPlanaVerticalKernelMajorant]
  exact Real.binetSecondFormula_kernel_majorant_integrableOn

/-- The Abel-Plana vertical kernel mass is nonnegative. -/
theorem Complex.binetAbelPlanaVerticalKernelMass_nonneg :
    0 ≤ Complex.binetAbelPlanaVerticalKernelMass := by
  dsimp [Complex.binetAbelPlanaVerticalKernelMass]
  exact
    setIntegral_nonneg
      measurableSet_Ioi
      Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi

/-- Explicit finite-contour majorant for the upper Abel-Plana endpoint
residual.

The standard finite-contour proof bounds the upper vertical residual by the
endpoint scale `O(1 / N)`.  The exponential factor belongs to the integration
kernel in the vertical variable, not to the endpoint parameter `N` itself. -/
noncomputable def Complex.binetAbelPlanaFiniteUpperContourResidualMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  8 * (1 + ‖w‖) ^ 2 *
    (1 + |Complex.binetAbelPlanaVerticalKernelMass|) / (N + 1 : ℝ)

/-- Explicit majorant for the lower Abel-Plana tail omitted by truncating the
lower boundary at height `N`.

This is intentionally a tail integral of the already-owned Binet vertical
kernel majorant.  The lower contour tail has exponential decay, but the
owner-level API available here proves decay through integrability of the
kernel, not through the upper-endpoint `O(1 / (N + 1))` scale used for the
finite upper residual. -/
noncomputable def Complex.binetAbelPlanaFiniteLowerContourTailMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  2 * ∫ t : ℝ in Set.Ioi (N : ℝ),
    Complex.binetAbelPlanaVerticalKernelMajorant t

/-- Explicit finite-contour majorant for the honest total Abel-Plana
remainder. -/
noncomputable def Complex.binetAbelPlanaFiniteContourRemainderMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N

/-- The upper endpoint-residual majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Tendsto
        (fun _N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|))
        atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|))) :=
    tendsto_const_nhds
  have hinv :
      Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          atTop
          atTop := by
      exact
        tendsto_atTop_add_const_right atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Tendsto
        (fun N : ℕ =>
          8 * (1 + ‖w‖) ^ 2 *
            (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
              ((N + 1 : ℝ))⁻¹)
        atTop
        (𝓝 (8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) * 0)) :=
    hconst.mul hinv
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) =
      (fun N : ℕ =>
        8 * (1 + ‖w‖) ^ 2 *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) *
            ((N + 1 : ℝ))⁻¹) := by
    funext N
    dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualMajorant]
    ring_nf
  exact
    (mul_zero (8 * (1 + ‖w‖) ^ 2 *
      (1 + |Complex.binetAbelPlanaVerticalKernelMass|))).symm ▸
      (heq ▸ hmul)

/-- The lower-tail majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  let K : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have htail :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 (∫ t : ℝ in ⋂ N : ℕ, Set.Ioi (N : ℝ), K t)) := by
    refine tendsto_setIntegral_of_antitone ?_ ?_ ?_
    · intro N
      exact measurableSet_Ioi
    · intro N M hNM
      exact Set.Ioi_subset_Ioi (by exact_mod_cast hNM)
    · exact
        ⟨0,
          Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn⟩
  have hInter :
      (⋂ N : ℕ, Set.Ioi (N : ℝ)) = (∅ : Set ℝ) := by
    ext t
    constructor
    · intro ht
      rcases exists_nat_gt t with ⟨N, hN⟩
      exact False.elim ((lt_asymm hN) (ht N))
    · intro ht
      exact False.elim ht
  have htail_zero :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 (0 : ℝ)) := by
    exact hInter ▸ htail
  have hscale :
      Tendsto
        (fun N : ℕ =>
          2 * ∫ t : ℝ in Set.Ioi (N : ℝ), K t)
        atTop
        (𝓝 ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul htail_zero
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) =
      (fun N : ℕ =>
        2 * ∫ t : ℝ in Set.Ioi (N : ℝ), K t) := by
    funext N
    rfl
  exact (mul_zero (2 : ℝ)).symm ▸ (heq ▸ hscale)

/-- The finite-contour majorant tends to zero. -/
theorem Complex.binetAbelPlanaFiniteContourRemainderMajorant_tendsto_zero
    (w : ℂ) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hlower :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
  have hupper :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hlower.add hupper
  have heq :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteContourRemainderMajorant w N) =
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N +
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) := by
    funext N
    rfl
  exact (zero_add (0 : ℝ)).symm ▸ (heq ▸ hsum)

/-- Exact finite Abel-Plana summation formula for the logarithmic summand. -/
theorem Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w := by
  exact
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_core
      hw

/-- Exact finite Abel-Plana residual identity for the logarithmic summand.

This is the finite contour theorem: after separating the finite main term and
the lower Abel-Plana boundary correction, the remaining error is exactly the
total contour remainder: lower truncation tail plus upper vertical residual. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      Complex.binetAbelPlanaFiniteRemainderError N w =
        Complex.binetAbelPlanaFiniteContourRemainder N w := by
  intro N
  have hfinite :
      Complex.binetAbelPlanaLogGammaFiniteApproximation N w =
        Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w :=
    Complex.binetAbelPlana_logGammaFiniteApproximation_eq_finiteMain_add_boundary_add_contourRemainder_owner
      hw N
  dsimp [Complex.binetAbelPlanaFiniteRemainderError]
  calc
    Complex.binetAbelPlanaLogGammaFiniteApproximation N w -
        (Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w)
        =
        (Complex.binetAbelPlanaFiniteMainTerm N w +
          Complex.binetAbelPlanaFiniteBoundaryCorrection N w +
            Complex.binetAbelPlanaFiniteContourRemainder N w) -
          (Complex.binetAbelPlanaFiniteMainTerm N w +
            Complex.binetAbelPlanaFiniteBoundaryCorrection N w) := by
          exact congrArg
            (fun z : ℂ =>
              z - (Complex.binetAbelPlanaFiniteMainTerm N w +
                Complex.binetAbelPlanaFiniteBoundaryCorrection N w))
            hfinite
    _ = Complex.binetAbelPlanaFiniteContourRemainder N w := by
          abel

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.abs_re_le_norm_owner
    (z : ℂ) :
    |z.re| ≤ ‖z‖ := by
  have habs : |z.re| ≤ Complex.abs z :=
    Complex.abs_re_le_abs z
  have hnorm : ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  exact Eq.subst
    (motive := fun r : ℝ => |z.re| ≤ r)
    hnorm.symm
    habs

/-- The real part of the upper endpoint line is the endpoint real part. -/
theorem Complex.binetAbelPlana_upperEndpointLine_re
    (w : ℂ)
    (N : ℕ)
    (s : ℝ) :
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re =
      w.re + (N + 1 : ℝ) := by
  calc
    (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re
        =
        (w + (N + 1 : ℂ)).re + ((s : ℂ) * Complex.I).re := by
          exact Complex.add_re (w + (N + 1 : ℂ)) ((s : ℂ) * Complex.I)
    _ = w.re + (N + 1 : ℝ) + ((s : ℂ) * Complex.I).re := by
          exact congrArg
            (fun r : ℝ => r + ((s : ℂ) * Complex.I).re)
            (Complex.add_re w (N + 1 : ℂ))
    _ = w.re + (N + 1 : ℝ) := by
          have hmul_re : ((s : ℂ) * Complex.I).re = 0 := by
            calc
              ((s : ℂ) * Complex.I).re
                  =
                  (s : ℂ).re * Complex.I.re -
                    (s : ℂ).im * Complex.I.im := by
                    exact Complex.mul_re (s : ℂ) Complex.I
          _ = 0 := by
                    norm_num
          linarith

/-- The upper endpoint line has norm bounded below by its positive real
coordinate. -/
theorem Complex.upperEndpointLine_endpoint_re_le_norm
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w.re + (N + 1 : ℝ) ≤
      ‖w + (N + 1 : ℂ) + (s : ℂ) * Complex.I‖ := by
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos N
  have hre_pos : 0 < z.re := by
    have hre :
        z.re = w.re + (N + 1 : ℝ) :=
      Complex.binetAbelPlana_upperEndpointLine_re w N s
    exact hre.symm ▸ add_pos hw hN_pos
  have h_re_abs : z.re = |z.re| :=
    (abs_of_pos hre_pos).symm
  calc
    w.re + (N + 1 : ℝ)
        = z.re := by
          exact
            (Complex.binetAbelPlana_upperEndpointLine_re w N s).symm
    _ = |z.re| :=
          h_re_abs
    _ ≤ ‖z‖ :=
          Complex.abs_re_le_norm_owner z

/-- The upper endpoint vertical line lies in the principal logarithm slit
plane. -/
theorem Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane := by
  have hre_pos :
      0 < (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I).re :=
    Complex.binetAbelPlanaUpperLogJumpSegmentDenominator_re_pos hw N s
  exact Or.inl hre_pos

/-- Real derivative of the principal logarithm along the upper endpoint
vertical line. -/
theorem Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (s : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
      (Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      s := by
  have hline :
      HasDerivAt
        (fun u : ℝ => w + (N + 1 : ℂ) + (u : ℂ) * Complex.I)
        Complex.I
        s := by
    fun_prop
  have hslit :
      w + (N + 1 : ℂ) + (s : ℂ) * Complex.I ∈ Complex.slitPlane :=
    Complex.binetAbelPlanaUpperEndpointLine_mem_slitPlane hw N s
  have hlog :
      HasDerivAt
        (fun u : ℝ =>
          Complex.log (w + (N + 1 : ℂ) + (u : ℂ) * Complex.I))
        (Complex.I /
          (w + (N + 1 : ℂ) + (s : ℂ) * Complex.I))
        s :=
    hline.clog_real hslit
  exact hlog

/-- The upper endpoint differential-log integrand is interval-integrable on
every finite segment. -/
theorem Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    IntervalIntegrable
      (fun s : ℝ =>
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s)
      volume
      a
      b := by
  dsimp [Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand]
  fun_prop

/-- Fundamental theorem of calculus for the upper endpoint logarithmic line. -/
theorem Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (a b : ℝ) :
    ∫ s : ℝ in a..b,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
      Complex.log (w + (N + 1 : ℂ) + (b : ℂ) * Complex.I) -
        Complex.log (w + (N + 1 : ℂ) + (a : ℂ) * Complex.I) := by
  exact
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _hs =>
        Complex.hasDerivAt_binetAbelPlanaUpperEndpointLine_log hw N s)
      (Complex.intervalIntegrable_binetAbelPlanaUpperLogJumpSegmentIntegrand
        hw N a b)

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      Complex.binetAbelPlanaFiniteUpperLogJump N w t =
        ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s := by
  filter_upwards with t
  have hftc :
      ∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s =
        Complex.log (w + (N + 1 : ℂ) + (t : ℂ) * Complex.I) -
          Complex.log (w + (N + 1 : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) :=
    Complex.integral_binetAbelPlanaUpperLogJumpSegmentIntegrand_eq_log_sub
      hw N (-t) t
  dsimp [Complex.binetAbelPlanaFiniteUpperLogJump]
  exact hftc
  congr 2
  ring

/-- Pointwise denominator estimate for the upper endpoint differential-log
segment integrand. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ s : ℝ,
      ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ := by
  intro s
  let z : ℂ := w + (N + 1 : ℂ) + (s : ℂ) * Complex.I
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos N
  have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
    add_pos hw hN_pos
  have hendpoint_le_norm :
      w.re + (N + 1 : ℝ) ≤ ‖z‖ :=
    Complex.upperEndpointLine_endpoint_re_le_norm hw N s
  have hinv_le :
      ‖z‖⁻¹ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
    calc
      ‖z‖⁻¹ = (1 : ℝ) / ‖z‖ := by
        exact inv_eq_one_div ‖z‖
      _ ≤ (1 : ℝ) / (w.re + (N + 1 : ℝ)) :=
        one_div_le_one_div_of_le hendpoint_pos hendpoint_le_norm
      _ = (w.re + (N + 1 : ℝ))⁻¹ := by
        exact (inv_eq_one_div (w.re + (N + 1 : ℝ))).symm
  calc
    ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        = ‖Complex.I / z‖ := by
          rfl
    _ = ‖Complex.I‖ / ‖z‖ := by
          exact norm_div Complex.I z
    _ = ‖z‖⁻¹ := by
          norm_num [Complex.norm_I, div_eq_mul_inv]
    _ ≤ (w.re + (N + 1 : ℝ))⁻¹ :=
          hinv_le

/-- Interval-length integration of the pointwise segment-integrand bound. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  have hpoint :
      ∀ s : ℝ,
        ‖Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (w.re + (N + 1 : ℝ))⁻¹ :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegrand_le_endpoint_re_inv
      hw N
  have hinterval :
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s hs => hpoint s)
  have habs : |t - (-t)| = 2 * t := by
    calc
      |t - (-t)| = |2 * t| := by
        ring_nf
      _ = 2 * t := abs_of_nonneg (mul_nonneg zero_le_two ht_nonneg)
  calc
    ‖∫ s : ℝ in (-t)..t,
        Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖
        ≤ (w.re + (N + 1 : ℝ))⁻¹ * |t - (-t)| := hinterval
    _ = (w.re + (N + 1 : ℝ))⁻¹ * (2 * t) := by
          exact congrArg
            (fun x : ℝ => (w.re + (N + 1 : ℝ))⁻¹ * x)
            habs
    _ = (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ := by
          ring

/-- Norm bound for the differential-log segment integral. -/
theorem Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖∫ s : ℝ in (-t)..t,
          Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
        (2 * t) / (w.re + (N + 1 : ℝ)) := by
  have hlength :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (2 * t) * (w.re + (N + 1 : ℝ))⁻¹ :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_length_mul_endpoint_re_inv
      hw N
  filter_upwards [hlength] with t ht
  change ‖∫ s : ℝ in (-t)..t,
      Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
    (2 * t) * (w.re + (N + 1 : ℝ))⁻¹
  exact ht

/-- Differential-log segment estimate for the upper Abel-Plana logarithmic
jump. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          (2 * t) / (w.re + (N + 1 : ℝ)) := by
  intro N
  have hidentity :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        Complex.binetAbelPlanaFiniteUpperLogJump N w t =
          ∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s :=
    Complex.binetAbelPlanaFiniteUpperLogJump_eq_segmentIntegral_owner hw N
  have hbound :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖∫ s : ℝ in (-t)..t,
            Complex.binetAbelPlanaUpperLogJumpSegmentIntegrand N w s‖ ≤
          (2 * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaUpperLogJumpSegmentIntegral_le_two_mul_t_div_endpoint_re
      hw N
  filter_upwards [hidentity, hbound] with t ht_eq ht_bound
  exact ht_eq ▸ ht_bound

/-- Endpoint real-part comparison for the upper Abel-Plana logarithmic jump. -/
theorem Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ t : ℝ,
      t ∈ Set.Ioi (0 : ℝ) →
        (2 * t) / (w.re + (N + 1 : ℝ)) ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  intro t ht
  have hN_pos : 0 < (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos N
  have hendpoint_pos : 0 < w.re + (N + 1 : ℝ) :=
    add_pos hw hN_pos
  have hone_le : 1 ≤ 1 + ‖w‖ :=
    le_add_of_nonneg_right (norm_nonneg w)
  have hbase :
      (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
        4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hden_le :
        (N + 1 : ℝ) ≤ w.re + (N + 1 : ℝ) :=
      le_add_of_nonneg_left hw.le
    have hrecip :
        (1 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          1 / (N + 1 : ℝ) := by
      exact one_div_le_one_div_of_le hN_pos hden_le
    have htwo :
        (2 : ℝ) / (w.re + (N + 1 : ℝ)) ≤
          2 / (N + 1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left hrecip zero_le_two
    have htwo_le_four :
        (2 : ℝ) / (N + 1 : ℝ) ≤
          4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
      have hnum : (2 : ℝ) ≤ 4 * (1 + ‖w‖) := by
        nlinarith [hone_le]
      exact div_le_div_of_nonneg_right hnum hN_pos.le
    exact htwo.trans htwo_le_four
  calc
    (2 * t) / (w.re + (N + 1 : ℝ))
        = ((2 : ℝ) / (w.re + (N + 1 : ℝ))) * t := by
          ring
    _ ≤ (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
          exact mul_le_mul_of_nonneg_right hbase ht.le

/-- Upper-endpoint logarithmic jump bound along the finite Abel-Plana
vertical contour. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t := by
  have hsegment :
      ∀ N : ℕ,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            (2 * t) / (w.re + (N + 1 : ℝ)) :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_two_mul_t_div_endpoint_re
      hw
  filter_upwards with N
  filter_upwards [hsegment N, ae_restrict_mem measurableSet_Ioi] with t ht_segment ht_mem
  exact
    ht_segment.trans
      (Complex.two_mul_t_div_upperEndpoint_re_le_public_logJump_majorant
        hw N t ht_mem)

/-- Pointwise majorization of the upper-contour residual integrand. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t := by
  have hjump :
      ∀ᶠ N : ℕ in atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ ≤
            (4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t :=
    Complex.norm_binetAbelPlanaFiniteUpperLogJump_le_endpoint_kernel hw
  filter_upwards [hjump] with N hN
  filter_upwards [hN, ae_restrict_mem measurableSet_Ioi] with t ht_jump ht_mem
  have ht_pos : 0 < t := ht_mem
  have hden_pos :
      0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    Real.binetSecondFormula_exp_denominator_pos ht_pos
  dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand]
  calc
      ‖Complex.I *
        (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
        =
        ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          calc
            ‖Complex.I *
                (Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
                = ‖Complex.I‖ *
                    ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact norm_mul _ _
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  norm_num [Complex.norm_I]
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
                  exact norm_div _ _
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ := by
                  exact congrArg (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                    (Complex.binetSecondFormula_exp_denominator_norm_eq t)
            _ = ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ /
                  (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
                  exact congrArg
                    (fun x : ℝ => ‖Complex.binetAbelPlanaFiniteUpperLogJump N w t‖ / x)
                    (Real.binetSecondFormula_exp_denominator_norm_eq ht_pos)
    _ ≤
        ((4 * (1 + ‖w‖) / (N + 1 : ℝ)) * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
          exact div_le_div_of_nonneg_right ht_jump hden_pos.le
    _ =
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMajorant t := by
          dsimp [Complex.binetAbelPlanaVerticalKernelMajorant]
          ring

/-- The norm of the upper finite Abel-Plana residual integrand is measurable
on the positive vertical half-line. -/
theorem Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand
    (N : ℕ)
    (w : ℂ) :
    AEStronglyMeasurable
      (fun t : ℝ =>
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
  have hmeas :
      Measurable
        (fun t : ℝ =>
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖) := by
    fun_prop [Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand,
      Complex.binetAbelPlanaFiniteUpperLogJump]
  exact hmeas.aestronglyMeasurable

/-- Integrability of the upper-contour residual integrand norm follows from
the vertical-kernel majorant. -/
theorem Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    IntegrableOn
      (fun t : ℝ =>
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
      (Set.Ioi (0 : ℝ)) := by
  let c : ℝ := 4 * (1 + ‖w‖) / (N + 1 : ℝ)
  let K : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖
  let M : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have hmajorant_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
    Complex.aestronglyMeasurable_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand
      N w
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖K t‖ ≤ c * M t := by
    filter_upwards [hmajorant] with t ht
    have hK_nonneg : 0 ≤ K t :=
      norm_nonneg
        (Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t)
    have hK_norm : ‖K t‖ = K t := by
      exact Real.norm_of_nonneg hK_nonneg
    exact hK_norm ▸ ht
  exact
    hmajorant_integrable.mono' hK_meas hpointwise

/-- Integral transport from a pointwise upper-contour integrand majorant to
the vertical-kernel mass. -/
theorem Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hcoef_nonneg :
      0 ≤ 4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    have hN_pos : 0 < (N + 1 : ℝ) := by
      exact_mod_cast Nat.succ_pos N
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (le_trans zero_le_one
          (le_add_of_nonneg_right (norm_nonneg w))))
      hN_pos.le
  have hmajorant_integrable :
      IntegrableOn
        (fun t : ℝ =>
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.const_mul
      (4 * (1 + ‖w‖) / (N + 1 : ℝ))
  have hintegrable :
      IntegrableOn
        (fun t : ℝ =>
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖)
        (Set.Ioi (0 : ℝ)) :=
    Complex.integrableOn_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_of_majorant
      (w := w)
      (N := N)
      hmajorant
  have hmono :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t :=
    setIntegral_mono_ae_restrict
      hintegrable
      hmajorant_integrable
      hmajorant
  have hconst :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t =
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
    dsimp [Complex.binetAbelPlanaVerticalKernelMass]
    exact integral_const_mul
  exact hmono.trans_eq hconst

/-- Fixed-index integral comparison for the upper-contour residual. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
    {w : ℂ}
    {N : ℕ}
    (hmajorant :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMajorant t) :
    ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass := by
  have hnorm_integral :
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ := by
    exact
      (Complex.binetAbelPlanaFiniteUpperContourResidual_eq_integral_integrand
        (N := N) (w := w)).trans_le
        (norm_integral_le_integral_norm _)
  have hkernel_integral :
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.integral_norm_binetAbelPlanaFiniteUpperContourResidualIntegrand_le_kernelMass
      (w := w)
      (N := N)
      hmajorant
  exact hnorm_integral.trans hkernel_integral

/-- Integral-level upper-contour residual estimate in terms of the vertical
kernel mass. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass := by
  have hpointwise :
      ∀ᶠ N : ℕ in atTop,
        ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ‖Complex.binetAbelPlanaFiniteUpperContourResidualIntegrand N w t‖ ≤
            (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
              Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_integrand_le_majorant
      hw
  filter_upwards [hpointwise] with N hN
  exact
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_of_integrand_majorant
      (w := w)
      (N := N)
      hN

/-- The kernel-mass bound is dominated by the upper-residual majorant. -/
theorem Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
    (w : ℂ)
    (N : ℕ) :
    (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
        Complex.binetAbelPlanaVerticalKernelMass ≤
      Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hden_pos : 0 < (N + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos N
  have hone_le_scale : 1 ≤ 1 + ‖w‖ := by
    exact le_add_of_nonneg_right (norm_nonneg w)
  have hmass_le :
      Complex.binetAbelPlanaVerticalKernelMass ≤
        1 + |Complex.binetAbelPlanaVerticalKernelMass| := by
    exact
      (le_abs_self Complex.binetAbelPlanaVerticalKernelMass).trans
        (le_add_of_nonneg_left zero_le_one)
  have hcoef_nonneg :
      0 ≤ 4 * (1 + ‖w‖) / (N + 1 : ℝ) := by
    exact div_nonneg
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
        (le_trans zero_le_one hone_le_scale))
      hden_pos.le
  have hcoef_le :
      4 * (1 + ‖w‖) ≤ 8 * (1 + ‖w‖) ^ 2 := by
    nlinarith [hone_le_scale, sq_nonneg (1 + ‖w‖)]
  have hscaled_mass :
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          Complex.binetAbelPlanaVerticalKernelMass ≤
        (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) :=
    mul_le_mul_of_nonneg_left hmass_le hcoef_nonneg
  have hscaled_coef :
      (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) ≤
        (8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ)) *
          (1 + |Complex.binetAbelPlanaVerticalKernelMass|) := by
    have hdiv :
        4 * (1 + ‖w‖) / (N + 1 : ℝ) ≤
          8 * (1 + ‖w‖) ^ 2 / (N + 1 : ℝ) :=
      div_le_div_of_nonneg_right hcoef_le hden_pos.le
    exact
      mul_le_mul_of_nonneg_right hdiv
        (add_nonneg zero_le_one (abs_nonneg _))
  exact
    hscaled_mass.trans
      (hscaled_coef.trans
        (by
          dsimp [Complex.binetAbelPlanaFiniteContourRemainderMajorant]
          dsimp [Complex.binetAbelPlanaFiniteUpperContourResidualMajorant]
          ring_nf))

/-- Owner upper-contour residual estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in atTop,
      ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
        Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hkernel :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
          (4 * (1 + ‖w‖) / (N + 1 : ℝ)) *
            Complex.binetAbelPlanaVerticalKernelMass :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_kernelMass_owner
      hw
  filter_upwards [hkernel] with N hN
  exact
    hN.trans
      (Complex.binetAbelPlanaFiniteUpperContourResidual_kernelMass_bound_le_majorant
        w N)

/-- The lower finite Abel-Plana tail integrand equals twice the principal
Binet arctangent kernel on its positive vertical contour. -/
theorem Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
        (-Complex.I) *
          ((Complex.log (w + (t : ℂ) * Complex.I) -
              Complex.log (w - (t : ℂ) * Complex.I)) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) =
          2 *
            (Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  intro N
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht_pos : 0 < t :=
    lt_of_le_of_lt (Nat.cast_nonneg N) ht
  exact
    Complex.binetAbelPlana_logJump_integrand_eq_two_arctanKernel
      hw ht_pos

/-- Pointwise lower-tail domination by twice the Binet vertical kernel
majorant. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
            ‖(-Complex.I) *
              ((Complex.log (w + (t : ℂ) * Complex.I) -
                  Complex.log (w - (t : ℂ) * Complex.I)) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ ≤
              C * Complex.binetAbelPlanaVerticalKernelMajorant t := by
  rcases
      Complex.binetSecondFormula_arctanKernel_tail_norm_le_majorant_owner
        hw with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨2 * C, mul_nonneg zero_le_two hC_nonneg, ?_⟩
  rcases exists_nat_gt (‖w‖ / 2) with ⟨N₀, hN₀⟩
  filter_upwards [eventually_ge_atTop N₀] with N hN
  filter_upwards
    [Complex.binetAbelPlanaFiniteLowerContourTail_integrand_eq_two_arctanKernel
      hw N,
      ae_restrict_mem measurableSet_Ioi] with t ht_eq ht_mem
  have hN₀_le_N : (N₀ : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN
  have ht_tail : t ∈ Set.Ioi (‖w‖ / 2) := by
    exact lt_of_lt_of_le hN₀ (le_trans hN₀_le_N (le_of_lt ht_mem))
  have hkernel :
      ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        C * Complex.binetAbelPlanaVerticalKernelMajorant t :=
    hC t ht_tail
  have hmajorant_nonneg :
      0 ≤ Complex.binetAbelPlanaVerticalKernelMajorant t :=
    Complex.binetAbelPlanaVerticalKernelMajorant_nonneg_on_Ioi
      t
      (lt_of_lt_of_le hN₀
        (le_trans hN₀_le_N (le_of_lt ht_mem)))
  calc
    ‖(-Complex.I) *
        ((Complex.log (w + (t : ℂ) * Complex.I) -
            Complex.log (w - (t : ℂ) * Complex.I)) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
        =
        ‖2 *
          (Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖ := by
          exact congrArg norm ht_eq
    _ =
        2 *
          ‖Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
          have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by
            norm_num [Complex.normSq]
          calc
            ‖2 *
              (Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))‖
                =
                ‖(2 : ℂ)‖ *
                  ‖Complex.arctan ((t : ℂ) / w) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact norm_mul _ _
            _ =
                2 *
                  ‖Complex.arctan ((t : ℂ) / w) /
                    (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
                  exact congrArg
                    (fun x : ℝ =>
                      x *
                        ‖Complex.arctan ((t : ℂ) / w) /
                          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖)
                    htwo
    _ ≤ 2 * (C * Complex.binetAbelPlanaVerticalKernelMajorant t) := by
          exact mul_le_mul_of_nonneg_left hkernel zero_le_two
    _ = (2 * C) * Complex.binetAbelPlanaVerticalKernelMajorant t := by
          ring

/-- Integral comparison for the omitted lower Abel-Plana tail. -/
theorem Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  rcases
      Complex.norm_binetAbelPlanaFiniteLowerContourTail_integrand_le_majorant
        hw with
    ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hC] with N hN
  let I : ℝ → ℂ := fun t : ℝ =>
    (-Complex.I) *
      ((Complex.log (w + (t : ℂ) * Complex.I) -
          Complex.log (w - (t : ℂ) * Complex.I)) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
  let K : ℝ → ℝ := fun t : ℝ =>
    Complex.binetAbelPlanaVerticalKernelMajorant t
  have htail_subset :
      Set.Ioi (N : ℝ) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_le_of_lt (Nat.cast_nonneg N) ht
  have hCK_integrable :
      IntegrableOn (fun t : ℝ => C * K t) (Set.Ioi (N : ℝ)) :=
    (Complex.binetAbelPlanaVerticalKernelMajorant_integrableOn.mono_set
      htail_subset).const_mul C
  have hnorm_meas :
      AEStronglyMeasurable (fun t : ℝ => ‖I t‖)
        (volume.restrict (Set.Ioi (N : ℝ))) := by
    have hmeas : Measurable (fun t : ℝ => ‖I t‖) := by
      fun_prop [I]
    exact hmeas.aestronglyMeasurable
  have hnorm_integrable :
      IntegrableOn (fun t : ℝ => ‖I t‖) (Set.Ioi (N : ℝ)) := by
    have hpointwise :
        ∀ᵐ t ∂volume.restrict (Set.Ioi (N : ℝ)),
          ‖‖I t‖‖ ≤ C * K t := by
      filter_upwards [hN] with t ht
      have hnorm_nonneg : 0 ≤ ‖I t‖ := norm_nonneg _
      exact (Real.norm_of_nonneg hnorm_nonneg) ▸ ht
    exact hCK_integrable.mono' hnorm_meas hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioi (N : ℝ), ‖I t‖ ≤
        ∫ t : ℝ in Set.Ioi (N : ℝ), C * K t :=
    setIntegral_mono_ae_restrict
      hnorm_integrable
      hCK_integrable
      hN
  have hconst :
      ∫ t : ℝ in Set.Ioi (N : ℝ), C * K t =
        C * ∫ t : ℝ in Set.Ioi (N : ℝ), K t := by
    exact integral_const_mul
  have hnorm_integral :
      ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
        ∫ t : ℝ in Set.Ioi (N : ℝ), ‖I t‖ := by
    dsimp [Complex.binetAbelPlanaFiniteLowerContourTail, I]
    exact norm_integral_le_integral_norm _
  exact hnorm_integral.trans (hmono.trans_eq hconst)

/-- Owner lower-tail estimate in fixed-ray kernel-tail form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t := by
  exact
    Complex.norm_binetAbelPlanaFiniteLowerContourTail_le_tailKernelMass
      hw

/-- Owner estimate for the honest total finite Abel-Plana contour remainder.

The total remainder is the sum of the lower truncation tail and the upper
endpoint residual.  This theorem is the analytic tail estimate replacing the
old false upper-only remainder bridge. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t +
              Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  rcases
      Complex.exists_norm_binetAbelPlanaFiniteLowerContourTail_le_kernelTail_owner
        hw with
    ⟨C, hC_nonneg, hlower⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hupper :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ ≤
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
    Complex.norm_binetAbelPlanaFiniteUpperContourResidual_le_majorant_owner hw
  filter_upwards [hlower, hupper] with N hN_lower hN_upper
  calc
    ‖Complex.binetAbelPlanaFiniteContourRemainder N w‖
        ≤
        ‖Complex.binetAbelPlanaFiniteLowerContourTail N w‖ +
          ‖Complex.binetAbelPlanaFiniteUpperContourResidual N w‖ := by
          dsimp [Complex.binetAbelPlanaFiniteContourRemainder]
          exact norm_add_le
            (Complex.binetAbelPlanaFiniteLowerContourTail N w)
            (Complex.binetAbelPlanaFiniteUpperContourResidual N w)
    _ ≤
        C * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t +
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
          exact add_le_add hN_lower hN_upper

/-- Owner finite-contour remainder estimate in majorant form. -/
theorem Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ᶠ N : ℕ in atTop,
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
            C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t +
              Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N := by
  have hidentity :
      ∀ N : ℕ,
        Complex.binetAbelPlanaFiniteRemainderError N w =
          Complex.binetAbelPlanaFiniteContourRemainder N w :=
    Complex.binetAbelPlanaFiniteRemainderError_eq_contourRemainder_owner
      hw
  rcases
      Complex.exists_norm_binetAbelPlanaFiniteContourRemainder_le_kernelTail_add_upperMajorant_owner
        hw with
    ⟨C, hC_nonneg, hbound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  filter_upwards [hbound] with N hN
  exact hidentity N ▸ hN

/-- Norm convergence from a fixed-ray lower kernel-tail estimate and the
upper-endpoint majorant estimate. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
    {w : ℂ}
    {C : ℝ}
    (hC_nonneg : 0 ≤ C)
    (hbound :
      ∀ᶠ N : ℕ in atTop,
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N) :
    Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hlower_tail :
      Tendsto
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        atTop
        (𝓝 (0 : ℝ)) := by
    have hmajorant :
        Tendsto
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N)
          atTop
          (𝓝 (0 : ℝ)) :=
      Complex.binetAbelPlanaFiniteLowerContourTailMajorant_tendsto_zero w
    have hscale :
        Tendsto
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)
          atTop
          (𝓝 (0 : ℝ)) := by
      have heq :
          (fun N : ℕ =>
            Complex.binetAbelPlanaFiniteLowerContourTailMajorant w N) =
          (fun N : ℕ =>
            (2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t) := by
        funext N
        rfl
      exact heq ▸ hmajorant
    have hinv :
        Tendsto
          (fun N : ℕ =>
            (1 / 2 : ℝ) *
              ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
                Complex.binetAbelPlanaVerticalKernelMajorant t))
          atTop
          (𝓝 ((1 / 2 : ℝ) * 0)) :=
      tendsto_const_nhds.mul hscale
    have heq_tail :
        (fun N : ℕ =>
          (1 / 2 : ℝ) *
            ((2 : ℝ) * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t)) =
        (fun N : ℕ =>
          ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t) := by
      funext N
      ring
    exact (mul_zero (1 / 2 : ℝ)).symm ▸ (heq_tail ▸ hinv)
  have hlower_scaled :
      Tendsto
        (fun N : ℕ =>
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
            Complex.binetAbelPlanaVerticalKernelMajorant t)
        atTop
        (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul hlower_tail
  have hupper :
      Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFiniteUpperContourResidualMajorant_tendsto_zero w
  have hsum :
      Tendsto
        (fun N : ℕ =>
          C * ∫ t : ℝ in Set.Ioi (N : ℝ),
              Complex.binetAbelPlanaVerticalKernelMajorant t +
            Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N)
        atTop
        (𝓝 (C * 0 + 0)) :=
    hlower_scaled.add hupper
  exact
    squeeze_zero'
      (Eventually.of_forall
        (fun N : ℕ =>
          norm_nonneg
            (Complex.binetAbelPlanaFiniteRemainderError N w)))
      hbound
      ((by ring : C * 0 + 0 = (0 : ℝ)) ▸ hsum)

/-- Norm decay of the finite Abel-Plana contour remainder.

This is the finite-contour estimate for the logarithmic summand.  It is stated
as norm convergence because the classical proof bounds the top and vertical
finite-contour residuals before passing to the complex limit. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hnorm_bound :
      ∃ C : ℝ,
        0 ≤ C ∧
          ∀ᶠ N : ℕ in atTop,
            ‖Complex.binetAbelPlanaFiniteRemainderError N w‖ ≤
              C * ∫ t : ℝ in Set.Ioi (N : ℝ),
                  Complex.binetAbelPlanaVerticalKernelMajorant t +
                Complex.binetAbelPlanaFiniteUpperContourResidualMajorant w N :=
    Complex.exists_norm_binetAbelPlanaFiniteRemainderError_le_kernelTail_add_upperMajorant_owner
      hw
  rcases hnorm_bound with ⟨C, hC_nonneg, hbound⟩
  exact
    Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_of_kernelTail_add_upperMajorant
      hC_nonneg
      hbound

/-- Algebraic/topological assembly of complex convergence from norm decay of
the finite Abel-Plana contour remainder. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
    {w : ℂ}
    (hnorm :
      Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaFiniteRemainderError N w‖)
        atTop
        (𝓝 (0 : ℝ))) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm

/-- Finite Abel-Plana contour-remainder decay in complex form. -/
theorem Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_from_contourNorm_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteRemainderError N w)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    Complex.binetAbelPlanaFiniteRemainderError_tendsto_zero_of_norm_tendsto_zero
      (Complex.binetAbelPlanaFiniteRemainderError_norm_tendsto_zero_owner hw)

end

end LFunctions
end Boundary
