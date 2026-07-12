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

/-- The shifted-correlation majorant is an affine function of the reciprocal
shift in endpoint-scale coordinates. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_eq_affine_invShift
    (T : ℝ)
    (b h : ℕ) :
    Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h =
      (4 + 4 * Real.pi) *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) *
              ((h : ℝ)⁻¹)) +
        4 := by
  let X : ℝ :=
    (((((b + 1 : ℕ) : ℝ) *
        (((b + 1 : ℕ) : ℝ))) / T) *
      ((h : ℝ)⁻¹))
  have hmajorant :
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h =
        4 * (X + 1) + 4 * Real.pi * X :=
    Real.secondDerivativeVdc_shiftedCorrelationMajorant_eq_endpointScale_invShift
      T b h
  have halgebra :
      4 * (X + 1) + 4 * Real.pi * X =
        (4 + 4 * Real.pi) * X + 4 := by
    calc
      4 * (X + 1) + 4 * Real.pi * X =
          (4 * X + 4 * 1) + 4 * Real.pi * X := by
        exact congrArg
          (fun r : ℝ => r + 4 * Real.pi * X)
          (mul_add 4 X 1)
      _ = (4 * X + 4) + 4 * Real.pi * X := by
        exact congrArg
          (fun r : ℝ => (4 * X + r) + 4 * Real.pi * X)
          (mul_one 4)
      _ = (4 * X + 4 * Real.pi * X) + 4 :=
        add_right_comm (4 * X) 4 (4 * Real.pi * X)
      _ = ((4 + 4 * Real.pi) * X) + 4 := by
        exact congrArg
          (fun r : ℝ => r + 4)
          ((add_mul 4 (4 * Real.pi) X).symm)
  exact Eq.trans hmajorant halgebra

/-- The summed shifted-correlation majorant separates into the reciprocal
shift sum and the constant shift-count term. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_sum_eq_affine_invShift
    (T : ℝ)
    (b H : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) =
      (4 + 4 * Real.pi) *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) *
            (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
              ((h : ℝ)⁻¹))) +
        (H : ℝ) * 4 := by
  let shifts : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_shiftRange H
  let C : ℝ := 4 + 4 * Real.pi
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / T
  let S : ℝ := ∑ h ∈ shifts, ((h : ℝ)⁻¹)
  have hpoint :
      (∑ h ∈ shifts,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) =
        ∑ h ∈ shifts, (C * (E * ((h : ℝ)⁻¹)) + 4) :=
    Finset.sum_congr
      (Eq.refl shifts)
      (fun h _hh =>
        Real.secondDerivativeVdc_shiftedCorrelationMajorant_eq_affine_invShift
          T b h)
  have hsplit :
      (∑ h ∈ shifts, (C * (E * ((h : ℝ)⁻¹)) + 4)) =
        (∑ h ∈ shifts, C * (E * ((h : ℝ)⁻¹))) +
          ∑ h ∈ shifts, 4 :=
    Finset.sum_add_distrib
  have hscaled_recip :
      (∑ h ∈ shifts, C * (E * ((h : ℝ)⁻¹))) =
        C * (E * S) := by
    have hC :
        (∑ h ∈ shifts, C * (E * ((h : ℝ)⁻¹))) =
          C * ∑ h ∈ shifts, E * ((h : ℝ)⁻¹) :=
      (Finset.mul_sum shifts (fun h : ℕ => E * ((h : ℝ)⁻¹)) C).symm
    have hE :
        (∑ h ∈ shifts, E * ((h : ℝ)⁻¹)) =
          E * S :=
      (Finset.mul_sum shifts (fun h : ℕ => ((h : ℝ)⁻¹)) E).symm
    exact Eq.trans hC (congrArg (fun r : ℝ => C * r) hE)
  have hconst :
      (∑ h ∈ shifts, 4) = (H : ℝ) * 4 :=
    Complex.realPhase_secondDerivative_vdc_shiftRange_sum_const H 4
  calc
    (∑ h ∈ shifts,
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) =
        ∑ h ∈ shifts, (C * (E * ((h : ℝ)⁻¹)) + 4) :=
      hpoint
    _ =
        (∑ h ∈ shifts, C * (E * ((h : ℝ)⁻¹))) +
          ∑ h ∈ shifts, 4 :=
      hsplit
    _ = C * (E * S) + ∑ h ∈ shifts, 4 := by
      exact congrArg
        (fun r : ℝ => r + ∑ h ∈ shifts, 4)
        hscaled_recip
    _ = C * (E * S) + (H : ℝ) * 4 := by
      exact congrArg
        (fun r : ℝ => C * (E * S) + r)
        hconst
    _ =
        (4 + 4 * Real.pi) *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) *
            (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
              ((h : ℝ)⁻¹))) +
          (H : ℝ) * 4 :=
      Eq.refl _

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

/-- The one-shift endpoint-scale majorant is nonnegative. -/
theorem Real.secondDerivativeVdc_endpointScale_oneShiftMajorant_nonneg
    {T : ℝ}
    (hT : 1 ≤ T)
    (b : ℕ) :
    0 ≤
      4 *
          (((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) +
            1) +
        4 * Real.pi *
          ((((b + 1 : ℕ) : ℝ) *
              (((b + 1 : ℕ) : ℝ))) / T) := by
  let E : ℝ :=
    ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / T)
  have hE_nonneg : 0 ≤ E := by
    have hnum_nonneg :
        0 ≤ (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) :=
      mul_nonneg
        (Nat.cast_nonneg (b + 1))
        (Nat.cast_nonneg (b + 1))
    have hT_nonneg : 0 ≤ T :=
      le_trans zero_le_one hT
    exact div_nonneg hnum_nonneg hT_nonneg
  have hfirst_inner_nonneg : 0 ≤ E + 1 :=
    add_nonneg hE_nonneg zero_le_one
  have hfirst_nonneg : 0 ≤ 4 * (E + 1) :=
    mul_nonneg zero_le_four hfirst_inner_nonneg
  have hfour_pi_nonneg : 0 ≤ 4 * Real.pi :=
    mul_nonneg zero_le_four Real.pi_nonneg
  have hsecond_nonneg : 0 ≤ 4 * Real.pi * E :=
    mul_nonneg hfour_pi_nonneg hE_nonneg
  exact add_nonneg hfirst_nonneg hsecond_nonneg

/-- At the canonical Weyl shift length, the summed shifted-correlation
majorants are bounded by the endpoint-plus-square-root target times the
one-shift endpoint-scale majorant. -/
theorem Real.secondDerivativeVdc_shiftedCorrelationMajorant_sum_weylShiftLength_le_target_mul_endpointScale
    {T : ℝ}
    (hT : 1 ≤ T)
    (b : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
        (Real.secondDerivativeVdc_weylShiftLength T),
      Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
      (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) *
        (4 *
            (((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ))) / T) +
              1) +
          4 * Real.pi *
            ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ))) / T)) := by
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength T
  let M : ℝ :=
    4 *
        (((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))) / T) +
          1) +
      4 * Real.pi *
        ((((b + 1 : ℕ) : ℝ) *
            (((b + 1 : ℕ) : ℝ))) / T)
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
        (H : ℝ) * M :=
    Real.secondDerivativeVdc_shiftedCorrelationMajorant_sum_le_length_mul_endpointScale
      hT b H
  have hH_target :
      (H : ℝ) ≤ (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) :=
    Real.secondDerivativeVdc_weylShiftLength_le_target (b := b) hT
  have hM_nonneg : 0 ≤ M :=
    Real.secondDerivativeVdc_endpointScale_oneShiftMajorant_nonneg hT b
  have hmul :
      (H : ℝ) * M ≤
        (((b + 1 : ℕ) : ℝ) / T + Real.sqrt (1 + T)) * M :=
    mul_le_mul_of_nonneg_right hH_target hM_nonneg
  exact le_trans hsum hmul

/-! A reusable arithmetic sink for the final Weyl radicand. -/

/-- A nonnegative Weyl radicand has the unavoidable diagonal lower bound
`A² / H`.  This is the feasibility check for any proposed square target. -/
theorem Real.secondDerivativeVdc_sq_mul_inv_le_radicand
    {A H E : ℝ}
    (hA : 0 ≤ A)
    (hH : 0 < H)
    (hE : 0 ≤ E) :
    A ^ 2 * H⁻¹ ≤ (A + H) * ((A + 2 * E) * H⁻¹) := by
  have hH_nonneg : 0 ≤ H := le_of_lt hH
  have hH_inv_nonneg : 0 ≤ H⁻¹ := inv_nonneg.mpr hH_nonneg
  have hA_le_first : A ≤ A + H :=
    le_add_of_nonneg_right hH_nonneg
  have htwoE_nonneg : 0 ≤ 2 * E :=
    mul_nonneg zero_le_two hE
  have hA_le_second : A ≤ A + 2 * E :=
    le_add_of_nonneg_right htwoE_nonneg
  have hscaled : A * H⁻¹ ≤ (A + 2 * E) * H⁻¹ :=
    mul_le_mul_of_nonneg_right hA_le_second hH_inv_nonneg
  have hproduct :
      A * (A * H⁻¹) ≤ (A + H) * ((A + 2 * E) * H⁻¹) :=
    mul_le_mul hA_le_first hscaled
      (mul_nonneg hA hH_inv_nonneg)
      (add_nonneg hA hH_nonneg)
  have hleft : A * (A * H⁻¹) = A ^ 2 * H⁻¹ := by
    exact
      Eq.trans
        (mul_assoc A A H⁻¹).symm
        (congrArg (fun square : ℝ => square * H⁻¹) (pow_two A).symm)
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤ (A + H) * ((A + 2 * E) * H⁻¹))
      hleft
      hproduct

theorem Real.secondDerivativeVdc_radicand_le_sq_of_factor_bounds
    {A H E M : ℝ}
    (hA : 0 ≤ A)
    (hH : 0 < H)
    (hM : 0 ≤ M)
    (hfirst : A + H ≤ M)
    (hsecond : A + 2 * E ≤ M * H) :
    (A + H) * ((A + 2 * E) * H⁻¹) ≤ M ^ 2 := by
  have hH_nonneg : 0 ≤ H := hH.le
  have hH_inv_nonneg : 0 ≤ H⁻¹ := inv_nonneg.mpr hH_nonneg
  have hsecond_scaled :
      (A + 2 * E) * H⁻¹ ≤ (M * H) * H⁻¹ :=
    mul_le_mul_of_nonneg_right hsecond hH_inv_nonneg
  have hH_ne : H ≠ 0 := ne_of_gt hH
  have hscaled_eq : (M * H) * H⁻¹ = M := by
    calc
      (M * H) * H⁻¹ = M * (H * H⁻¹) :=
        mul_assoc M H H⁻¹
      _ = M * 1 := congrArg (fun value : ℝ => M * value) (mul_inv_cancel₀ hH_ne)
      _ = M := mul_one M
  have hsecond_final : (A + 2 * E) * H⁻¹ ≤ M :=
    Eq.subst
      (motive := fun value : ℝ => (A + 2 * E) * H⁻¹ ≤ value)
      hscaled_eq
      hsecond_scaled
  have hfirst_nonneg : 0 ≤ A + H := add_nonneg hA hH_nonneg
  have hproduct :
      (A + H) * ((A + 2 * E) * H⁻¹) ≤ (A + H) * M :=
    mul_le_mul_of_nonneg_left hsecond_final hfirst_nonneg
  have hM_sq : (A + H) * M ≤ M * M :=
    mul_le_mul_of_nonneg_right hfirst hM
  exact
    le_trans hproduct
      (Eq.subst
        (motive := fun value : ℝ => (A + H) * M ≤ value)
        (pow_two M).symm
        hM_sq)

end

end LFunctions
end Boundary
