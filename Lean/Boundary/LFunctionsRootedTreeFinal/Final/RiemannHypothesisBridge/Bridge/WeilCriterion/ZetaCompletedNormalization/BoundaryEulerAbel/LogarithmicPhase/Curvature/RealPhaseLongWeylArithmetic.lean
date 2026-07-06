import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongWeylTarget

/-!
# Real-phase long Weyl arithmetic

This file owns small finite arithmetic estimates for the explicit
curvature-majorant Weyl target.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The reciprocal of the shifted lower parameter factors as the endpoint
curvature scale times the reciprocal shift. -/
theorem Real.secondDerivativeVdc_shiftedLowerParameter_inv_eq
    (T : ℝ)
    (b h : ℕ) :
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (h : ℝ))⁻¹ =
      ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ))) / T) *
        ((h : ℝ)⁻¹) := by
  let Bsq : ℝ :=
    (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ)))
  calc
    (T * Bsq⁻¹ * (h : ℝ))⁻¹ =
        ((h : ℝ)⁻¹) * (T * Bsq⁻¹)⁻¹ :=
      mul_inv_rev (T * Bsq⁻¹) (h : ℝ)
    _ = ((h : ℝ)⁻¹) * ((Bsq⁻¹)⁻¹ * T⁻¹) := by
      exact congrArg
        (fun r : ℝ => ((h : ℝ)⁻¹) * r)
        (mul_inv_rev T Bsq⁻¹)
    _ = ((h : ℝ)⁻¹) * (Bsq * T⁻¹) := by
      exact congrArg
        (fun r : ℝ => ((h : ℝ)⁻¹) * (r * T⁻¹))
        (inv_inv Bsq)
    _ = (Bsq * T⁻¹) * ((h : ℝ)⁻¹) :=
      mul_comm ((h : ℝ)⁻¹) (Bsq * T⁻¹)
    _ = (Bsq / T) * ((h : ℝ)⁻¹) := by
      exact congrArg
        (fun r : ℝ => r * ((h : ℝ)⁻¹))
        (div_eq_mul_inv Bsq T).symm

/-- The shifted-correlation majorant in endpoint-scale reciprocal-shift
coordinates. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_eq_endpointScale_invShift
    (T : ℝ)
    (b h : ℕ) :
    Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h =
      4 *
          ((((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) *
              ((h : ℝ)⁻¹)) +
            1) +
        4 * Real.pi *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) *
            ((h : ℝ)⁻¹)) := by
  let A : ℝ :=
    (T *
        ((((b + 1 : ℕ) : ℝ) *
          (((b + 1 : ℕ) : ℝ)))⁻¹) *
        (h : ℝ))⁻¹
  let B : ℝ :=
    (((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ))) / T) *
      ((h : ℝ)⁻¹))
  have hAB : A = B :=
    Real.secondDerivativeVdc_shiftedLowerParameter_inv_eq T b h
  show 4 * (A + 1) + 4 * Real.pi * A =
      4 * (B + 1) + 4 * Real.pi * B
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        4 * (A + 1) + 4 * Real.pi * A =
          4 * (r + 1) + 4 * Real.pi * r)
      hAB
      rfl

/-- Each positive Weyl shift has reciprocal at most one. -/
theorem Real.secondDerivativeVdc_shiftRange_inv_le_one
    {H h : ℕ}
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    ((h : ℝ)⁻¹) ≤ 1 := by
  have hh_one_nat : 1 ≤ h :=
    Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh
  have hh_one_cast : ((1 : ℕ) : ℝ) ≤ (h : ℝ) :=
    Nat.cast_le.mpr hh_one_nat
  have hh_one_real : (1 : ℝ) ≤ (h : ℝ) :=
    Eq.subst
      (motive := fun r : ℝ => r ≤ (h : ℝ))
      Nat.cast_one
      hh_one_cast
  exact inv_le_one_of_one_le₀ hh_one_real

/-- Each shifted-correlation majorant is bounded by replacing `h⁻¹` with
one in endpoint-scale coordinates. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_le_endpointScale_one
    {T : ℝ}
    (hT : 1 ≤ T)
    {b H h : ℕ}
    (hh : h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H) :
    Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h ≤
      4 *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) +
            1) +
        4 * Real.pi *
          ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) := by
  let E : ℝ :=
    ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / T)
  let u : ℝ := ((h : ℝ)⁻¹)
  have hE_nonneg : 0 ≤ E := by
    have hnum_nonneg :
        0 ≤ (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) :=
      mul_nonneg
        (Nat.cast_nonneg (b + 1))
        (Nat.cast_nonneg (b + 1))
    have hT_nonneg : 0 ≤ T :=
      le_trans zero_le_one hT
    exact div_nonneg hnum_nonneg hT_nonneg
  have hu_le_one : u ≤ 1 :=
    Real.secondDerivativeVdc_shiftRange_inv_le_one hh
  have hEu_le_E : E * u ≤ E :=
    Eq.subst
      (motive := fun r : ℝ => E * u ≤ r)
      (mul_one E)
      (mul_le_mul_of_nonneg_left hu_le_one hE_nonneg)
  have hfirst_inner :
      E * u + 1 ≤ E + 1 :=
    add_le_add_right hEu_le_E 1
  have hfirst :
      4 * (E * u + 1) ≤ 4 * (E + 1) :=
    mul_le_mul_of_nonneg_left hfirst_inner zero_le_four
  have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
    mul_nonneg zero_le_four Real.pi_nonneg
  have hsecond :
      4 * Real.pi * (E * u) ≤ 4 * Real.pi * E :=
    mul_le_mul_of_nonneg_left hEu_le_E hfour_pi_nonneg
  have hnormalized :
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h =
        4 * (E * u + 1) + 4 * Real.pi * (E * u) :=
    Real.secondDerivativeVdc_shiftedCorrelationMajorant_eq_endpointScale_invShift
      T b h
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 4 * (E + 1) + 4 * Real.pi * E)
      hnormalized.symm
      (add_le_add hfirst hsecond)

/-- The reciprocal sum over the Weyl shift range is bounded by the shift
length. -/
theorem Real.secondDerivativeVdc_shiftRange_inv_sum_le_length
    (H : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ((h : ℝ)⁻¹)) ≤ (H : ℝ) := by
  have hsum_le :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((h : ℝ)⁻¹)) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (1 : ℝ) :=
    Finset.sum_le_sum
      (fun h hh =>
        Real.secondDerivativeVdc_shiftRange_inv_le_one hh)
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (1 : ℝ)) = (H : ℝ) :=
    Eq.trans
      (Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const H 1)
      (mul_one (H : ℝ))
  exact le_trans hsum_le (le_of_eq hconst)

/-- The explicit shifted-correlation curvature majorants are bounded by the
shift length times the endpoint-scale one-shift majorant. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_sum_le_length_mul_endpointScale
    {T : ℝ}
    (hT : 1 ≤ T)
    (b H : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
      (H : ℝ) *
        (4 *
            (((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ))) / T) +
              1) +
          4 * Real.pi *
            ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ))) / T)) := by
  let M : ℝ :=
    4 *
        (((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))) / T) +
          1) +
      4 * Real.pi *
        ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))) / T)
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h ≤ M :=
    fun h hh =>
      Real.secondDerivativeVdc_shiftedCorrelationMajorant_le_endpointScale_one
        hT hh
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M :=
    Finset.sum_le_sum hpoint
  have hconst :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H, M) =
        (H : ℝ) * M :=
    Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const H M
  exact le_trans hsum (le_of_eq hconst)

end

end LFunctions
end Boundary
