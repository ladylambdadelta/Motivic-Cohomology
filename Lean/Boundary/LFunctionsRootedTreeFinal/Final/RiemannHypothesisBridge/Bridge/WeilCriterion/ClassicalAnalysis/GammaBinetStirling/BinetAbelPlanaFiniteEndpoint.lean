import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteAlgebra

/-!
# Finite Abel-Plana endpoint owners

This file owns the endpoint Taylor/Stirling estimates and endpoint-main-term convergence.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

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
    exact Real.inv_one_sub_le_two_of_le_half hsmall
  have herror :
      ‖Complex.binetEndpointLogTaylorError w M‖ =
        ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
          Complex.binetEndpointSmallVariable w M‖ := by
    exact congrArg norm (Complex.binetEndpointLogTaylorError_unfold w M)
  calc
    ‖Complex.binetEndpointLogTaylorError w M‖ =
        ‖Complex.log (1 + Complex.binetEndpointSmallVariable w M) -
          Complex.binetEndpointSmallVariable w M‖ := herror
    _ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 *
          (1 - ‖Complex.binetEndpointSmallVariable w M‖)⁻¹ / 2 := hraw
    _ ≤ ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 * 2 / 2 := by
      exact
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hden
            (sq_nonneg ‖Complex.binetEndpointSmallVariable w M‖))
          zero_le_two
    _ = ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 := by
      exact Real.mul_two_div_two
        (‖Complex.binetEndpointSmallVariable w M‖ ^ 2)

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
    exact Nat.cast_ne_zero.mpr hM
  have hsmall :
      ‖Complex.binetEndpointSmallVariable w M‖ ≤ (1 / 2 : ℝ) := by
    have hhalf : ‖w‖ ≤ (1 / 2 : ℝ) * (M : ℝ) := by
      exact Real.le_half_mul_of_two_mul_one_add_le
        (norm_nonneg w)
        hlarge
    calc
      ‖Complex.binetEndpointSmallVariable w M‖ = ‖w‖ / (M : ℝ) :=
        Complex.norm_binetEndpointSmallVariable_eq w M
      _ ≤ (1 / 2 : ℝ) :=
        (div_le_iff₀ hMpos_real).mpr hhalf
  have htaylor :
      ‖Complex.binetEndpointLogTaylorError w M‖ ≤
        ‖Complex.binetEndpointSmallVariable w M‖ ^ 2 :=
    Complex.norm_binetEndpointLogTaylorError_le_square hsmall
  have hsmall_norm :
      ‖Complex.binetEndpointSmallVariable w M‖ =
        ‖w‖ / (M : ℝ) := by
    exact Complex.norm_binetEndpointSmallVariable_eq w M
  have hnormal :
      Complex.binetAbelPlanaEndpointLogShiftError w M =
        -((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
          (w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M :=
    Complex.binetAbelPlanaEndpointLogShiftError_eq_taylor_normal_form hM hw
  have hfirst :
      ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) := by
    have hdiv_norm :
        ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ =
          ‖w * (w + (1 / 2 : ℂ))‖ / (M : ℝ) :=
      Complex.norm_div_natCast (w * (w + (1 / 2 : ℂ))) M
    have hnum :
        ‖w * (w + (1 / 2 : ℂ))‖ ≤ (1 + ‖w‖) ^ 2 := by
      calc
        ‖w * (w + (1 / 2 : ℂ))‖
            = ‖w‖ * ‖w + (1 / 2 : ℂ)‖ := norm_mul _ _
        _ ≤ ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) := by
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg w)
        _ ≤ (1 + ‖w‖) ^ 2 := by
          have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) :=
            Complex.norm_one_div_two
          have htransport :
              ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) =
                ‖w‖ * (‖w‖ + (1 / 2 : ℝ)) := by
            exact congrArg
              (fun y : ℝ => ‖w‖ * (‖w‖ + y))
              hhalf_norm
          calc
            ‖w‖ * (‖w‖ + ‖(1 / 2 : ℂ)‖) =
                ‖w‖ * (‖w‖ + (1 / 2 : ℝ)) := htransport
            _ ≤ (1 + ‖w‖) ^ 2 :=
              Real.mul_add_half_le_one_add_sq (norm_nonneg w)
    calc
      ‖(w * (w + (1 / 2 : ℂ))) / (M : ℂ)‖ =
          ‖w * (w + (1 / 2 : ℂ))‖ / (M : ℝ) := hdiv_norm
      _ ≤ (1 + ‖w‖) ^ 2 / (M : ℝ) :=
        div_le_div_of_nonneg_right hnum hMpos_real.le
  have hsecond :
      ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖ ≤
        3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
    have hendpoint :
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ ≤
          (3 / 2 : ℝ) * (M : ℝ) := by
      calc
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖
            ≤ ‖w‖ + ‖(M : ℂ)‖ + ‖(1 / 2 : ℂ)‖ := by
              exact (norm_add_le (w + (M : ℂ)) (1 / 2 : ℂ)).trans
                (add_le_add_right (norm_add_le w (M : ℂ)) ‖(1 / 2 : ℂ)‖)
        _ = ‖w‖ + (M : ℝ) + (1 / 2 : ℝ) := by
              have hM_norm : ‖(M : ℂ)‖ = (M : ℝ) :=
                Complex.norm_natCast M
              have hhalf_norm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) :=
                Complex.norm_one_div_two
              exact congrArg₂ HAdd.hAdd
                (congrArg₂ HAdd.hAdd rfl hM_norm)
                hhalf_norm
        _ ≤ (3 / 2 : ℝ) * (M : ℝ) := by
              exact Real.endpoint_add_half_le_three_halves
                (norm_nonneg w)
                hlarge
    have htailor_bound :
        ‖Complex.binetEndpointLogTaylorError w M‖ ≤
          (‖w‖ / (M : ℝ)) ^ 2 := by
      exact hsmall_norm.symm ▸ htaylor
    have hendpoint_majorant_nonneg :
        0 ≤ (3 / 2 : ℝ) * (M : ℝ) :=
      mul_nonneg
        (div_nonneg
          (le_trans zero_le_two Real.two_le_three_asymptotics)
          zero_le_two)
        hMpos_real.le
    calc
      ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
          Complex.binetEndpointLogTaylorError w M‖ =
        ‖w + (M : ℂ) + (1 / 2 : ℂ)‖ *
          ‖Complex.binetEndpointLogTaylorError w M‖ := norm_mul _ _
      _ ≤
          ((3 / 2 : ℝ) * (M : ℝ)) *
            ((‖w‖ / (M : ℝ)) ^ 2) := by
        exact mul_le_mul hendpoint htailor_bound
          (norm_nonneg _)
          hendpoint_majorant_nonneg
      _ ≤ 3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
        have hMpos : 0 < (M : ℝ) := hMpos_real
        have hr_nonneg : 0 ≤ ‖w‖ := norm_nonneg w
        exact
          Real.endpoint_second_term_le_cubic_over_endpoint
            hMpos
            hr_nonneg
  exact hnormal ▸ by
    calc
      ‖-((w * (w + (1 / 2 : ℂ))) / (M : ℂ)) -
          (w + (M : ℂ) + (1 / 2 : ℂ)) *
            Complex.binetEndpointLogTaylorError w M‖
          ≤
        ‖((w * (w + (1 / 2 : ℂ))) / (M : ℂ))‖ +
            ‖(w + (M : ℂ) + (1 / 2 : ℂ)) *
              Complex.binetEndpointLogTaylorError w M‖ := by
            exact Complex.norm_neg_sub_le_add_norm
              ((w * (w + (1 / 2 : ℂ))) / (M : ℂ))
              ((w + (M : ℂ) + (1 / 2 : ℂ)) *
                Complex.binetEndpointLogTaylorError w M)
      _ ≤
        (1 + ‖w‖) ^ 2 / (M : ℝ) +
          3 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          exact add_le_add hfirst hsecond
      _ ≤ 4 * (1 + ‖w‖) ^ 3 / (M : ℝ) := by
          have hMpos : 0 < (M : ℝ) := hMpos_real
          have hone : 1 ≤ 1 + ‖w‖ := by
            exact le_add_of_nonneg_right (norm_nonneg w)
          exact
            Real.endpoint_square_cube_sum_le_four_cube hMpos.le hone

/-- Exact algebraic endpoint decomposition: the finite endpoint remainder is
the sum of the factorial Stirling error and the branch-safe endpoint shift
error. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift_algebra
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteMainTerm N w -
        Complex.binetLogGammaMainTerm w =
      Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1) := by
  have hmain :
      Complex.binetAbelPlanaFiniteMainTerm N w =
        let M : ℕ := N + 1
        w * Complex.log (M : ℂ) + Complex.log ((Nat.factorial M : ℕ) : ℂ) -
          (((w + (M : ℂ)) * Complex.log (w + (M : ℂ)) - (w + (M : ℂ))) -
            (w * Complex.log w - w)) -
          (Complex.log w + Complex.log (w + (M : ℂ))) / 2 :=
    Complex.binetAbelPlanaFiniteMainTerm_unfold N w
  have hlimit :
      Complex.binetLogGammaMainTerm w =
        (w - (1 / 2 : ℂ)) * Complex.log w - w +
          (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2 :=
    Complex.binetLogGammaMainTerm_unfold w
  have hfactorial :
      Complex.binetAbelPlanaFactorialStirlingError (N + 1) =
        Complex.log ((Nat.factorial (N + 1) : ℕ) : ℂ) -
          ((((N + 1 : ℕ) : ℂ) + (1 / 2 : ℂ)) *
              Complex.log ((N + 1 : ℕ) : ℂ) -
            ((N + 1 : ℕ) : ℂ) +
              (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2) :=
    Complex.binetAbelPlanaFactorialStirlingError_unfold (N + 1)
  have hshift :
      Complex.binetAbelPlanaEndpointLogShiftError w (N + 1) =
        ((w + ((N + 1 : ℕ) : ℂ) + (1 / 2 : ℂ)) *
            (Complex.log ((N + 1 : ℕ) : ℂ) -
              Complex.log (w + ((N + 1 : ℕ) : ℂ)))) +
          w :=
    Complex.binetAbelPlanaEndpointLogShiftError_unfold w (N + 1)
  exact hmain ▸ hlimit ▸ hfactorial.symm ▸ hshift.symm ▸ by
    exact
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_unfolded_regroup
        w ((N + 1 : ℕ) : ℂ)
        (Complex.log ((N + 1 : ℕ) : ℂ))
        (Complex.log w)
        (Complex.log (w + ((N + 1 : ℕ) : ℂ)))
        (Complex.log ((Nat.factorial (N + 1) : ℕ) : ℂ))
        (((Real.log (2 * Real.pi)) : ℝ) : ℂ)

/-- Exact algebraic endpoint decomposition: the finite endpoint remainder is
the sum of the factorial Stirling error and the branch-safe endpoint shift
error. -/
theorem Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w =
      Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1) := by
  have hendpoint_unfold :
      Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w =
        Complex.binetAbelPlanaFiniteMainTerm N w -
          Complex.binetLogGammaMainTerm w :=
    Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_core_unfold N w
  exact
    Eq.trans hendpoint_unfold
      (Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift_algebra
        w N)

/-- Factorial Stirling error majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaFactorialStirlingMajorant
    (N : ℕ) : ℝ :=
  (1 : ℝ) / (N + 1 : ℝ)

/-- Definition unfolding for the factorial Stirling endpoint majorant. -/
theorem Complex.binetAbelPlanaFactorialStirlingMajorant_unfold
    (N : ℕ) :
    Complex.binetAbelPlanaFactorialStirlingMajorant N =
      (1 : ℝ) / (N + 1 : ℝ) := rfl

/-- Endpoint logarithmic-shift majorant for the endpoint decomposition. -/
noncomputable def Complex.binetAbelPlanaEndpointLogShiftMajorant
    (w : ℂ)
    (N : ℕ) : ℝ :=
  4 * (1 + ‖w‖) ^ 3 / (N + 1 : ℝ)

/-- Definition unfolding for the endpoint logarithmic-shift majorant. -/
theorem Complex.binetAbelPlanaEndpointLogShiftMajorant_unfold
    (w : ℂ)
    (N : ℕ) :
    Complex.binetAbelPlanaEndpointLogShiftMajorant w N =
      4 * (1 + ‖w‖) ^ 3 / (N + 1 : ℝ) := rfl

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
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hinv :
      Filter.Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Filter.Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          Filter.atTop
          Filter.atTop := by
      exact
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hevent :
      (fun N : ℕ => ((N + 1 : ℝ))⁻¹) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Eq.trans
          (Complex.binetAbelPlanaFactorialStirlingMajorant_unfold N)
          (one_div (N + 1 : ℝ))).symm)
  exact hinv.congr' hevent

/-- The endpoint logarithmic-shift majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero
    (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hconst :
      Filter.Tendsto
        (fun _N : ℕ => 4 * (1 + ‖w‖) ^ 3)
        Filter.atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3)) :=
    tendsto_const_nhds
  have hinv :
      Filter.Tendsto
        (fun N : ℕ => ((N + 1 : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (0 : ℝ)) := by
    have hshift :
        Filter.Tendsto
          (fun N : ℕ => (N + 1 : ℝ))
          Filter.atTop
          Filter.atTop := by
      exact
        Filter.tendsto_atTop_add_const_right Filter.atTop (1 : ℝ)
          tendsto_natCast_atTop_atTop
    exact tendsto_inv_atTop_zero.comp hshift
  have hmul :
      Filter.Tendsto
        (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹)
        Filter.atTop
        (𝓝 (4 * (1 + ‖w‖) ^ 3 * 0)) :=
    hconst.mul hinv
  have hevent :
      (fun N : ℕ => 4 * (1 + ‖w‖) ^ 3 * ((N + 1 : ℝ))⁻¹) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Eq.trans
          (Complex.binetAbelPlanaEndpointLogShiftMajorant_unfold w N)
          (div_eq_mul_inv
            (4 * (1 + ‖w‖) ^ 3)
            (N + 1 : ℝ))).symm)
  exact (mul_zero (4 * (1 + ‖w‖) ^ 3)).symm ▸ (hmul.congr' hevent)

/-- The endpoint-Stirling majorant tends to zero. -/
theorem Complex.binetAbelPlanaEndpointStirlingMajorant_tendsto_zero
    (w : ℂ) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N)
      Filter.atTop
      (𝓝 (0 : ℝ)) := by
  have hfactorial :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaFactorialStirlingMajorant_tendsto_zero
  have hshift :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingMajorant N +
            Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        Filter.atTop
        (𝓝 ((0 : ℝ) + 0)) :=
    hfactorial.add hshift
  have hevent :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingMajorant N +
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointStirlingMajorant w N) :=
    Filter.Eventually.of_forall
      (fun _N => rfl)
  exact (zero_add (0 : ℝ)).symm ▸ (hsum.congr' hevent)

/-- The factorial Stirling component tends to zero by mathlib's Stirling
formula. -/
theorem Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1))
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  have hreal :
      Filter.Tendsto
        (fun N : ℕ =>
          Real.binetAbelPlanaFactorialStirlingError (N + 1))
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Real.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ =>
          (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ))
        Filter.atTop
        (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp hreal
  have hevent :
      (fun N : ℕ =>
        (Real.binetAbelPlanaFactorialStirlingError (N + 1) : ℂ)) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1)) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Complex.binetAbelPlanaFactorialStirlingError_eq_ofReal
          (N + 1)
          (Nat.succ_ne_zero N)).symm)
  exact hcomplex.congr' hevent

/-- Owner logarithmic-shift estimate in majorant form. -/
theorem Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ᶠ N : ℕ in Filter.atTop,
      ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
        Complex.binetAbelPlanaEndpointLogShiftMajorant w N := by
  have hlarge :
      ∀ᶠ N : ℕ in Filter.atTop,
        2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact
      (Filter.eventually_ge_atTop (Nat.ceil (2 * (1 + ‖w‖)))).mono
        (fun N hN =>
          by
            have hceil :
                2 * (1 + ‖w‖) ≤ ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) :=
              Nat.le_ceil (2 * (1 + ‖w‖))
            have hNreal :
                ((Nat.ceil (2 * (1 + ‖w‖))) : ℝ) ≤ (N : ℝ) :=
              Nat.cast_le.mpr hN
            have hN_le_succ : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
              Nat.cast_le.mpr (Nat.le_succ N)
            exact hceil.trans (hNreal.trans hN_le_succ))
  exact
    hlarge.mono
      (fun N hNlarge =>
        by
          have hM_ne : N + 1 ≠ 0 := Nat.succ_ne_zero N
          have hlarge_M :
              2 * (1 + ‖w‖) ≤ ((N + 1 : ℕ) : ℝ) :=
            hNlarge
          have hraw :
              ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
                4 * (1 + ‖w‖) ^ 3 / ((N + 1 : ℕ) : ℝ) :=
            Complex.norm_binetAbelPlanaEndpointLogShiftError_le_large_endpoint_majorant
              hM_ne hw hlarge_M
          have hden :
              ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 :=
            Eq.trans
              (Nat.cast_add N 1)
              (congrArg (fun x : ℝ => (N : ℝ) + x) Nat.cast_one)
          have hraw_public :
              ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
                4 * (1 + ‖w‖) ^ 3 / ((N : ℝ) + 1) :=
            hraw.trans_eq
              (congrArg
                (fun d : ℝ => 4 * (1 + ‖w‖) ^ 3 / d)
                hden)
          exact
            (Complex.binetAbelPlanaEndpointLogShiftMajorant_unfold w N).symm ▸
              hraw_public)

/-- The endpoint logarithmic-shift component tends to zero from its explicit
majorant. -/
theorem Complex.binetAbelPlanaEndpointLogShiftError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  have hbound :
      ∀ᶠ N : ℕ in Filter.atTop,
        ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖ ≤
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N :=
    Complex.norm_binetAbelPlanaEndpointLogShiftError_le_majorant_owner hw
  have hmajorant :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftMajorant w N)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    Complex.binetAbelPlanaEndpointLogShiftMajorant_tendsto_zero w
  have hnorm :
      Filter.Tendsto
        (fun N : ℕ =>
          ‖Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)‖)
        Filter.atTop
        (𝓝 (0 : ℝ)) :=
    squeeze_zero'
      (Filter.Eventually.of_forall
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
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        Filter.atTop
        (𝓝 (0 : ℂ)))
    (hshift :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        Filter.atTop
        (𝓝 (0 : ℂ))) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
            Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        Filter.atTop
        (𝓝 ((0 : ℂ) + 0)) :=
    hfactorial.add hshift
  have hevent :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFactorialStirlingError (N + 1) +
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1)) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w) :=
    Filter.Eventually.of_forall
      (fun N =>
        (Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_eq_factorial_add_shift
          w N).symm)
  exact (zero_add (0 : ℂ)).symm ▸ (hsum.congr' hevent)

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
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
      Filter.atTop
      (𝓝 (0 : ℂ)) := by
  have hfactorial :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFactorialStirlingError (N + 1))
        Filter.atTop
        (𝓝 (0 : ℂ)) :=
    Complex.binetAbelPlanaFactorialStirlingError_tendsto_zero_owner
  have hshift :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaEndpointLogShiftError w (N + 1))
        Filter.atTop
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
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w)
        Filter.atTop
        (𝓝 (0 : ℂ))) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      Filter.atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
            Complex.binetLogGammaMainTerm w)
        Filter.atTop
        (𝓝 (0 + Complex.binetLogGammaMainTerm w)) :=
    hendpoint.add tendsto_const_nhds
  have hfinite_event :
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteEndpointStirlingRemainder N w +
          Complex.binetLogGammaMainTerm w) =ᶠ[Filter.atTop]
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w) :=
    Filter.Eventually.of_forall
      (fun N =>
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
              (Complex.binetLogGammaMainTerm w))
  have htarget :
      (0 : ℂ) + Complex.binetLogGammaMainTerm w =
        Complex.binetLogGammaMainTerm w :=
    zero_add (Complex.binetLogGammaMainTerm w)
  exact htarget ▸ (hsum.congr' hfinite_event)

/-- Finite endpoint/Stirling asymptotic in the concrete finite-main-term
form. -/
theorem Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_from_endpointStirling_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    Filter.Tendsto
      (fun N : ℕ =>
        Complex.binetAbelPlanaFiniteMainTerm N w)
      Filter.atTop
      (𝓝 (Complex.binetLogGammaMainTerm w)) := by
  exact
    Complex.binetAbelPlanaFiniteMainTerm_tendsto_binetMainTerm_of_endpointStirlingRemainder
      (Complex.binetAbelPlanaFiniteEndpointStirlingRemainder_tendsto_zero_owner
        hw)

end

end LFunctions
end Boundary
