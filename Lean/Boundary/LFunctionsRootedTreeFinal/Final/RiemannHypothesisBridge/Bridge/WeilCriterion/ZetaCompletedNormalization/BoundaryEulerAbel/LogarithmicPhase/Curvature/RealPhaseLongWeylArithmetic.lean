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

/-- Pointwise shifted-correlation majorants control the weighted Weyl
positive-difference mass without replacing the weight `H - h` by `H`. -/
theorem Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass_le_weightedMajorants
    (φ : ℝ → ℝ)
    (a b H : ℕ)
    (M : ℕ → ℝ)
    (hbound :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤
            M h) :
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
        φ a b H ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - h : ℕ) : ℝ) * M h := by
  show
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ((H - h : ℕ) : ℝ) *
        ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖) ≤
      ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - h : ℕ) : ℝ) * M h
  exact
    Finset.sum_le_sum
      (fun h hh =>
        mul_le_mul_of_nonneg_left
          (hbound h hh)
          (Nat.cast_nonneg (H - h)))

/-- The exact weighted curvature-majorant mass is controlled by the shift
length times the unweighted curvature-majorant envelope. -/
theorem Real.secondDerivativeVdc_weightedShiftedCorrelationMajorant_sum_le_length_mul_sum
    {T : ℝ}
    (hT : 1 ≤ T)
    (b H : ℕ) :
    (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
      ((H - h : ℕ) : ℝ) *
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
      (H : ℝ) *
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) := by
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ((H - h : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h ≤
            (H : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h := by
    intro h hh
    have hsub_le : H - h ≤ H :=
      Nat.sub_le H h
    have hmajorant_nonneg :
        0 ≤ Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h :=
      Real.secondDerivativeVdc_shiftedCorrelationMajorant_nonneg hT
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
    exact
      mul_le_mul_of_nonneg_right
        (Nat.cast_le.mpr hsub_le)
        hmajorant_nonneg
  have hsum :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - h : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          (H : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h :=
    Finset.sum_le_sum hpoint
  have hfactor :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        (H : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) =
        (H : ℝ) *
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) :=
    (Finset.mul_sum
      (Complex.realPhase_secondDerivative_vdc_shiftRange H)
      (fun h : ℕ =>
        Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h)
      (H : ℝ)).symm
  exact le_trans hsum (le_of_eq hfactor)

/-- The weighted Weyl envelope built from curvature majorants is bounded by
the ordinary Weyl envelope built from their unweighted sum. -/
theorem Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_curvatureMajorants_le_weylEnvelopeMajorant_sum
    {T : ℝ}
    (hT : 1 ≤ T)
    {a b H : ℕ}
    (hH : 1 ≤ H) :
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((H - h : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
      Real.secondDerivativeVdc_weylEnvelopeMajorant a b H
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) := by
  have hmass :
      (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
        ((H - h : ℕ) : ℝ) *
          Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) ≤
        (H : ℝ) *
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            Real.secondDerivativeVdc_shiftedCorrelationMajorant T b h) :=
    Real.secondDerivativeVdc_weightedShiftedCorrelationMajorant_sum_le_length_mul_sum
      hT b H
  exact
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_le_weylEnvelope_of_le_H_mul
      hH hmass

/-- Logarithmic Weyl-envelope bound with exact Weyl weights retained in the
curvature-majorant positive-difference mass. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_le_weightedWeylEnvelope_curvatureMajorants
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b
        (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
        (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
          (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
            Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let H : ℕ := Real.secondDerivativeVdc_weylShiftLength ‖t‖
  let M : ℕ → ℝ :=
    fun h : ℕ =>
      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h
  have hH :
      1 ≤ H :=
    Real.one_le_secondDerivativeVdc_weylShiftLength ht
  have hH_block :
      H ≤ (Finset.Icc a b).card :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_card_of_sqrt_long
      ht hab hlong_sqrt
  have hgap :
      H ≤ b - a :=
    Nat.secondDerivativeVdc_weylShiftLength_le_block_gap_of_sqrt_long
      ht hlong_sqrt
  have habh :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          a ≤ b - h :=
    fun h hh =>
      Nat.realPhase_secondDerivative_vdc_lower_le_sub_shift hgap hh
  have hderiv_lower :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ∀ x : ℝ,
            x ∈ Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ) →
              ‖t‖ *
                  ((((b + 1 : ℕ) : ℝ) *
                    (((b + 1 : ℕ) : ℝ)))⁻¹) *
                  (h : ℝ) ≤
                ‖deriv
                  (Complex.realPhase_secondDerivative_vdc_shiftedDifference φ h) x‖ :=
    fun h hh x hx =>
      Complex.logarithmicPhaseRealPhase_shiftedDifference_deriv_norm_lower_on_shifted_Icc
        t ha
        (le_trans
          (Complex.realPhase_secondDerivative_vdc_shiftRange_le hh)
          hgap)
        hx hderiv_growth
  have hpoint :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H →
          ‖Complex.realPhase_secondDerivative_vdc_shiftedCorrelation φ h a b‖ ≤
            M h :=
    fun h hh =>
      Complex.realPhase_secondDerivative_vdc_shiftedCorrelation_bound_of_curvatureScale_data
        φ ht ha
        (Complex.realPhase_secondDerivative_vdc_shiftRange_pos hh)
        (habh h hh)
        (hderiv_antitone h hh)
        (hderiv_lower h hh)
        (hinc_mono h hh)
        (hred_mono h hh)
        (hsep h hh)
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H) :=
    @Complex.realPhase_secondDerivative_vdc_original_sum_norm_le_weightedWeylEnvelope
      φ a b H hH hH_block
  have hmass :
      Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
          φ a b H ≤
        ∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
          ((H - h : ℕ) : ℝ) * M h :=
    Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass_le_weightedMajorants
      φ a b H M hpoint
  have hmajorant :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (Complex.realPhase_secondDerivative_vdc_weylTranslatePositiveDifferenceMass
            φ a b H) ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b H
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange H,
            ((H - h : ℕ) : ℝ) * M h) :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_mono hH hmass
  exact le_trans hweyl hmajorant

/-- The exact weighted logarithmic Weyl-envelope estimate gives the long
target once the weighted curvature-majorant envelope has been bounded by that
target. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hweighted_target :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hweyl :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) :=
    Complex.logarithmicPhaseRealPhase_block_norm_le_weightedWeylEnvelope_curvatureMajorants
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep
  exact le_trans hweyl hweighted_target

/-- Radicand form of the exact weighted logarithmic Weyl-envelope target. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_radicand_target
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u))
    (hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hrad :
      (Real.secondDerivativeVdc_blockLength a b +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              Real.secondDerivativeVdc_blockLength a b +
                2 *
                  (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                    (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                    (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have htarget_nonneg :
      0 ≤ 80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 80)
      (le_of_lt (Real.secondDerivativeVdc_target_pos (b := b) ht))
  have hweighted_target :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖))) :=
    Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant_le_of_radicand_le_sq
      htarget_nonneg
      hrad
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hweighted_target

/-- Positive-frequency weighted long Weyl-target wrapper with the parent
curvature growth and shifted-derivative antitonicity discharged. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_target_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hweighted_target :
      Real.secondDerivativeVdc_weightedWeylEnvelopeMajorant a b
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖)
          (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
              Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h) ≤
        80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u) :=
    Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
      t ht ht_nonneg ha hab
  have hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hweighted_target

/-- Positive-frequency weighted long Weyl-target wrapper with the parent
curvature growth and shifted-derivative antitonicity discharged, in radicand
form. -/
theorem Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_radicand_target_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hinc_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hred_mono :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_reducedIntegerIncrementMonotoneOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h))
    (hsep :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          Complex.realPhase_integerIncrementSeparatedOn
            (Complex.realPhase_secondDerivative_vdc_shiftedDifference
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              h)
            a (b - h)
            (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (h : ℝ)))
    (hrad :
      (Real.secondDerivativeVdc_blockLength a b +
          (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ)) *
          (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              Real.secondDerivativeVdc_blockLength a b +
                2 *
                  (∑ h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
                    (Real.secondDerivativeVdc_weylShiftLength ‖t‖),
                    (((Real.secondDerivativeVdc_weylShiftLength ‖t‖) - h : ℕ) : ℝ) *
                      Real.secondDerivativeVdc_shiftedCorrelationMajorant ‖t‖ b h)) *
            (((Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ) *
              (Real.secondDerivativeVdc_weylShiftLength ‖t‖ : ℝ))⁻¹)) ≤
        (80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
          Real.sqrt (1 + ‖t‖)))) ^ 2) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  have hderiv_growth :
      ∀ u v : ℝ,
        u ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        v ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
        u ≤ v →
          (‖t‖ *
              ((((b + 1 : ℕ) : ℝ) *
                (((b + 1 : ℕ) : ℝ)))⁻¹) *
              (v - u) ≤
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) v -
            deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) u) :=
    Complex.logarithmicPhaseRealPhase_deriv_growth_on_integer_block
      t ht ht_nonneg ha hab
  have hderiv_antitone :
      ∀ h : ℕ,
        h ∈ Complex.realPhase_secondDerivative_vdc_shiftRange
            (Real.secondDerivativeVdc_weylShiftLength ‖t‖) →
          AntitoneOn
            (fun x : ℝ =>
              ‖deriv
                (Complex.realPhase_secondDerivative_vdc_shiftedDifference
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  h) x‖)
            (Set.Icc (a : ℝ) (((b - h) + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_weylShift_deriv_norm_antitoneOn_of_nonneg
      t ht ht_nonneg ha hab hlong_sqrt
  exact
    Complex.logarithmicPhaseRealPhase_long_bound_of_weightedWeylEnvelope_radicand_target
      t ht ha hab hlong_sqrt hderiv_growth hderiv_antitone
      hinc_mono hred_mono hsep hrad

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

end

end LFunctions
end Boundary
