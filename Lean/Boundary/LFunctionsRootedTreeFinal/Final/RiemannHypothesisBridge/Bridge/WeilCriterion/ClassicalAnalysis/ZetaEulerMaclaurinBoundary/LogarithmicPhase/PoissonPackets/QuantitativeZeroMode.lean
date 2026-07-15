import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCrossings
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.Reconstruction

/-!
# Zero-frequency identities for quantitative logarithmic packets

The zero Fourier mode has no stationary point on a positive block.  This file
owns the exact normalization transports used before its direct integration by
parts estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Real.integerAngularFrequency_zero :
    Real.integerAngularFrequency 0 = 0 := by
  unfold Real.integerAngularFrequency
  have hcast : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
  calc
    2 * Real.pi * ((0 : ℤ) : ℝ) = 2 * Real.pi * 0 :=
      congrArg (fun value : ℝ => 2 * Real.pi * value) hcast
    _ = 0 := mul_zero (2 * Real.pi)

theorem Complex.realPhaseFrequencyTwist_zero
    (φ : ℝ → ℝ)
    (x : ℝ) :
    Complex.realPhaseFrequencyTwist φ 0 x = φ x := by
  unfold Complex.realPhaseFrequencyTwist
  have hcast : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
  calc
    φ x - 2 * Real.pi * ((0 : ℤ) : ℝ) * x =
        φ x - 2 * Real.pi * 0 * x :=
      congrArg (fun value : ℝ => φ x - 2 * Real.pi * value * x) hcast
    _ = φ x - 0 * x :=
      congrArg (fun value : ℝ => φ x - value * x) (mul_zero (2 * Real.pi))
    _ = φ x - 0 := congrArg (fun value : ℝ => φ x - value) (zero_mul x)
    _ = φ x := sub_zero (φ x)

theorem Complex.logarithmicPhaseFourierTwistedDerivative_zero
    (t x : ℝ) :
    Complex.logarithmicPhaseFourierTwistedDerivative t 0 x = -‖t‖ / x := by
  unfold Complex.logarithmicPhaseFourierTwistedDerivative
  exact
    Eq.trans
      (congrArg (fun value : ℝ => -‖t‖ / x - value)
        Real.integerAngularFrequency_zero)
      (sub_zero (-‖t‖ / x))

theorem Complex.logarithmicPhaseFourierStationaryPoint_zero
    (t : ℝ) :
    Complex.logarithmicPhaseFourierStationaryPoint t 0 = 0 := by
  unfold Complex.logarithmicPhaseFourierStationaryPoint
  have hcast : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
  calc
    ‖t‖ / (2 * Real.pi * (-((0 : ℤ) : ℝ))) =
        ‖t‖ / (2 * Real.pi * (-0)) :=
      congrArg (fun value : ℝ => ‖t‖ / (2 * Real.pi * (-value))) hcast
    _ = ‖t‖ / (2 * Real.pi * 0) :=
      congrArg (fun value : ℝ => ‖t‖ / (2 * Real.pi * value)) neg_zero
    _ = ‖t‖ / 0 := congrArg (fun value : ℝ => ‖t‖ / value) (mul_zero (2 * Real.pi))
    _ = 0 := div_zero ‖t‖

theorem Complex.logarithmicPhaseFourierTwistedDerivative_zero_neg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseFourierTwistedDerivative t 0 x < 0 := by
  have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hquotient_pos : 0 < ‖t‖ / x := div_pos ht_pos hx
  have hnegative : -‖t‖ / x < 0 := by
    exact
      Eq.subst
        (motive := fun value : ℝ => value < 0)
        (neg_div x ‖t‖).symm
        (neg_lt_zero.mpr hquotient_pos)
  exact
    Eq.subst
      (motive := fun value : ℝ => value < 0)
      (Complex.logarithmicPhaseFourierTwistedDerivative_zero t x).symm
      hnegative

theorem Complex.logarithmicPhaseFourierTwistedDerivative_zero_ne_zero
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseFourierTwistedDerivative t 0 x ≠ 0 := by
  exact ne_of_lt (Complex.logarithmicPhaseFourierTwistedDerivative_zero_neg t ht hx)

theorem Complex.logarithmicPhaseFourierZeroDerivativeDenominator_ne_zero
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.realPhaseDerivativeDenominator
      (Complex.logarithmicPhaseFourierTwistedDerivative t 0) x ≠ 0 := by
  unfold Complex.realPhaseDerivativeDenominator
  exact
    mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr
        (Complex.logarithmicPhaseFourierTwistedDerivative_zero_ne_zero t ht hx))

theorem Complex.logarithmicPhaseFourierZeroStationaryPoint_not_mem_positive
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    x ≠ Complex.logarithmicPhaseFourierStationaryPoint t 0 := by
  have hzero := Complex.logarithmicPhaseFourierStationaryPoint_zero t
  exact hzero ▸ ne_of_gt hx

theorem Complex.norm_logarithmicPhaseFourierTwistedDerivative_zero
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseFourierTwistedDerivative t 0 x‖ = ‖t‖ / x := by
  have htwisted := Complex.logarithmicPhaseFourierTwistedDerivative_zero t x
  have hx_norm : ‖x‖ = x := Real.norm_of_nonneg hx.le
  calc
    ‖Complex.logarithmicPhaseFourierTwistedDerivative t 0 x‖ = ‖-‖t‖ / x‖ :=
      congrArg norm htwisted
    _ = ‖-‖t‖‖ / ‖x‖ := norm_div (-‖t‖) x
    _ = ‖t‖ / ‖x‖ :=
      congrArg (fun value : ℝ => value / ‖x‖)
        ((norm_neg ‖t‖).trans (Real.norm_of_nonneg (norm_nonneg t)))
    _ = ‖t‖ / x := congrArg (fun value : ℝ => ‖t‖ / value) hx_norm

theorem Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t 0) x‖ =
      x / ‖t‖ := by
  have hcoefficient :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficient t 0 x
  have hderivative :=
    Complex.norm_logarithmicPhaseFourierTwistedDerivative_zero t hx
  have hratio_inv : (‖t‖ / x)⁻¹ = x / ‖t‖ := inv_div ‖t‖ x
  exact
    hcoefficient.trans
      ((congrArg Inv.inv hderivative).trans hratio_inv)

theorem Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_right
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {left right x : ℝ}
    (hleft : 0 < left)
    (hleft_right : left ≤ right)
    (hx : x ∈ Set.Icc left right) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t 0) x‖ ≤
      right / ‖t‖ := by
  have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hcoefficient :=
    Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient t ht
      (lt_of_lt_of_le hleft hx.1)
  have hquotient : x / ‖t‖ ≤ right / ‖t‖ :=
    div_le_div_of_nonneg_right hx.2 ht_pos.le
  exact hcoefficient.trans_le hquotient

theorem Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_left
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {left right : ℝ}
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t 0) left‖ ≤
      right / ‖t‖ := by
  exact
    Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_right
      t ht hleft hleft_right ⟨le_rfl, hleft_right⟩

theorem Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_two_right
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {left right : ℝ}
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t 0) right‖ +
      ‖Complex.realPhaseIntegrationCoefficient
        (Complex.logarithmicPhaseFourierTwistedDerivative t 0) left‖ ≤
      2 * (right / ‖t‖) := by
  have hright :=
    Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_right
      t ht hleft hleft_right ⟨hleft_right, le_rfl⟩
  have hleft_bound :=
    Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_left
      t ht hleft hleft_right
  have hsum := add_le_add hright hleft_bound
  have htwo : right / ‖t‖ + right / ‖t‖ = 2 * (right / ‖t‖) :=
    (two_mul (right / ‖t‖)).symm
  exact Eq.subst (motive := fun bound : ℝ => _ ≤ bound) htwo hsum

theorem Complex.logarithmicPhaseFourierZero_coefficientDerivative_scalar
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    (‖t‖ / x ^ 2) /
        (‖Complex.logarithmicPhaseFourierTwistedDerivative t 0 x‖ ^ 2) =
      ‖t‖⁻¹ := by
  have ht_pos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have ht_ne : ‖t‖ ≠ 0 := ne_of_gt ht_pos
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hx_sq_ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hx_ne
  have hderivative :=
    Complex.norm_logarithmicPhaseFourierTwistedDerivative_zero t hx
  have hpow : (‖t‖ / x) ^ 2 = ‖t‖ ^ 2 / x ^ 2 :=
    div_pow ‖t‖ x 2
  calc
    (‖t‖ / x ^ 2) /
        (‖Complex.logarithmicPhaseFourierTwistedDerivative t 0 x‖ ^ 2) =
        (‖t‖ / x ^ 2) / (‖t‖ / x) ^ 2 :=
      congrArg (fun value : ℝ => (‖t‖ / x ^ 2) / value)
        (congrArg (fun value : ℝ => value ^ 2) hderivative)
    _ = (‖t‖ / x ^ 2) / (‖t‖ ^ 2 / x ^ 2) :=
      congrArg (fun value : ℝ => (‖t‖ / x ^ 2) / value) hpow
    _ = ‖t‖ / ‖t‖ ^ 2 :=
      div_div_div_cancel_right₀ hx_sq_ne ‖t‖ (‖t‖ ^ 2)
    _ = ‖t‖ / (‖t‖ * ‖t‖) :=
      congrArg (fun value : ℝ => ‖t‖ / value) (pow_two ‖t‖)
    _ = ‖t‖ / ‖t‖ / ‖t‖ := div_mul_eq_div_div ‖t‖ ‖t‖ ‖t‖
    _ = 1 / ‖t‖ :=
      congrArg (fun value : ℝ => value / ‖t‖) (div_self ht_ne)
    _ = ‖t‖⁻¹ := one_div ‖t‖

theorem Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficientDerivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x‖ =
      ‖t‖⁻¹ := by
  have hnorm :=
    Complex.norm_logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x
  have hscalar :=
    Complex.logarithmicPhaseFourierZero_coefficientDerivative_scalar t ht hx
  exact hnorm.trans hscalar

theorem Complex.integral_norm_logarithmicPhaseFourierZeroCoefficientDerivative_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    (∫ x in left..right,
      ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x‖) ≤
      (right - left) • ‖t‖⁻¹ := by
  have hstationary :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t 0 :=
    fun x hx =>
      Complex.logarithmicPhaseFourierZeroStationaryPoint_not_mem_positive
        t (lt_of_lt_of_le hleft hx.1)
  have hintegrable :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg 0 left right hleft hleft_right hstationary
  have hnorm_integrable :
      IntervalIntegrable
        (fun x : ℝ =>
          ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x‖)
        volume left right :=
    hintegrable.norm
  have hconstant_nonneg : 0 ≤ ‖t‖⁻¹ := inv_nonneg.mpr (norm_nonneg t)
  have hpointwise :
      ∀ x ∈ Set.Icc left right,
        ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x‖ ≤
          ‖t‖⁻¹ := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le hleft hx.1
    exact le_of_eq
      (Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficientDerivative
        t ht hx_pos)
  exact
    Complex.integral_norm_le_constant_smul_length
      (Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0)
      left right ‖t‖⁻¹ hleft_right hconstant_nonneg hnorm_integrable hpointwise

theorem Complex.norm_intervalIntegral_logarithmicPhaseFourierZeroOscillation_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (left right : ℝ)
    (hleft : 0 < left)
    (hleft_right : left ≤ right) :
    ‖∫ x in left..right,
      Complex.realPhaseOscillation
        (Complex.realPhaseFrequencyTwist
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          0) x‖ ≤
      2 * (right / ‖t‖) + (right - left) • ‖t‖⁻¹ := by
  have hstationary_Icc :
      ∀ x ∈ Set.Icc left right,
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t 0 :=
    fun x hx =>
      Complex.logarithmicPhaseFourierZeroStationaryPoint_not_mem_positive
        t (lt_of_lt_of_le hleft hx.1)
  have hstationary :
      ∀ x ∈ [[left, right]],
        x ≠ Complex.logarithmicPhaseFourierStationaryPoint t 0 := by
    intro x hx
    have hinterval : [[left, right]] = Set.Icc left right := Set.uIcc_of_le hleft_right
    exact hstationary_Icc x (hinterval ▸ hx)
  have hcoefficient :=
    Complex.intervalIntegrable_logarithmicPhase_coefficientDerivative
      t ht ht_nonneg 0 left right hleft hleft_right hstationary_Icc
  have hoscillation :=
    Complex.intervalIntegrable_logarithmicPhase_oscillationDerivative
      t ht_nonneg 0 left right hleft hleft_right
  have hgeneric :=
    Complex.norm_intervalIntegral_logarithmicPhaseFourierOscillation_le_nonstationary_tail
      t ht ht_nonneg 0 left right hleft hleft_right hstationary hcoefficient hoscillation
  have hendpoints :=
    Complex.norm_logarithmicPhaseFourierZeroIntegrationCoefficient_le_two_right
      t ht hleft hleft_right
  have hremainder :=
    Complex.integral_norm_logarithmicPhaseFourierZeroCoefficientDerivative_le
      t ht ht_nonneg left right hleft hleft_right
  have hsum :
      ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t 0) right‖ +
        ‖Complex.realPhaseIntegrationCoefficient
          (Complex.logarithmicPhaseFourierTwistedDerivative t 0) left‖ +
        ∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t 0) x) ^ 2‖ ≤
        2 * (right / ‖t‖) + (right - left) • ‖t‖⁻¹ := by
    have htransport :
        (∫ x in left..right,
          ‖-(Complex.I * ((‖t‖ : ℂ) / (x : ℂ) ^ 2)) /
            (Complex.realPhaseDerivativeDenominator
              (Complex.logarithmicPhaseFourierTwistedDerivative t 0) x) ^ 2‖) =
          ∫ x in left..right,
            ‖Complex.logarithmicPhaseFourierIntegrationCoefficientDerivative t 0 x‖ := by
      exact intervalIntegral.integral_congr
        (fun x _hx => rfl)
    exact
      add_le_add hendpoints
        (Eq.subst
          (motive := fun remainder : ℝ =>
            remainder ≤ (right - left) • ‖t‖⁻¹)
          htransport
          hremainder)
  exact le_trans hgeneric hsum

theorem Complex.norm_add_three_le
    (left middle right : ℂ) :
    ‖left + middle + right‖ ≤ ‖left‖ + ‖middle‖ + ‖right‖ := by
  have hfirst := norm_add_le left (middle + right)
  have hsecond := norm_add_le middle right
  have hassociated :
      ‖left + (middle + right)‖ ≤
        ‖left‖ + ‖middle‖ + ‖right‖ := by
    have hsum := le_trans hfirst (add_le_add_left hsecond ‖left‖)
    exact Eq.subst
      (motive := fun value : ℝ =>
        ‖left + (middle + right)‖ ≤ value)
      (add_assoc ‖left‖ ‖middle‖ ‖right‖).symm
      hsum
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ ‖left‖ + ‖middle‖ + ‖right‖)
    (add_assoc left middle right).symm
    hassociated

theorem Complex.norm_add_three_reorder
    (left middle right : ℂ) :
    ‖left‖ + ‖middle‖ + ‖right‖ =
      (‖left‖ + ‖right‖) + ‖middle‖ := by
  calc
    ‖left‖ + ‖middle‖ + ‖right‖ =
        ‖left‖ + (‖middle‖ + ‖right‖) :=
      (add_assoc _ _ _)
    _ = ‖left‖ + (‖right‖ + ‖middle‖) :=
      congrArg (fun value : ℝ => ‖left‖ + value) (add_comm _ _)
    _ = (‖left‖ + ‖right‖) + ‖middle‖ :=
      (add_assoc _ _ _).symm

theorem Complex.zero_packet_budget_reassociate
    (crossing central tail : ℝ) :
    crossing + (central + tail) = crossing + central + tail :=
  (add_assoc _ _ _).symm

theorem Complex.norm_logarithmicPhaseQuantitativeZeroPacket_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b 0‖ ≤
      2 / 3 + 2 * ((b : ℝ) / ‖t‖) + ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ := by
  have ha_cast : ((1 : ℤ) : ℝ) = 1 := Int.cast_one
  have ha_real : (1 : ℝ) ≤ (a : ℝ) := ha_cast ▸ Int.cast_le.mpr ha
  have ha_pos : 0 < (a : ℝ) := lt_of_lt_of_le zero_lt_one ha_real
  have hab_real : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hdecomposition :=
    Complex.logarithmicPhaseQuantitativeBlockFourierPacket_eq_three_parts
      t a b 0 ha hab
  have hprincipal :=
    Complex.norm_intervalIntegral_logarithmicPhaseFourierZeroOscillation_le
      t ht ht_nonneg (a : ℝ) (b : ℝ) ha_pos hab_real
  have hcrossings :=
    Complex.norm_quantitativeLogarithmic_crossings_le_two_div_three t a b 0
  have htriangle :
      ‖(∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) 0 x) +
          (∫ x in (a : ℝ)..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                0) x) +
          (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (Real.quantitativeLogarithmicBlockCutoff a b) 0 x)‖ ≤
        ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ +
          ‖∫ x in (a : ℝ)..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                0) x‖ +
        ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ := by
    exact Complex.norm_add_three_le _ _ _
  have hcomponents :
      ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ +
          ‖∫ x in (a : ℝ)..(b : ℝ),
            Complex.realPhaseOscillation
              (Complex.realPhaseFrequencyTwist
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                0) x‖ +
          ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ ≤
        2 / 3 +
          (2 * ((b : ℝ) / ‖t‖) + ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹) := by
    have hsum := add_le_add hcrossings hprincipal
    have hreorder :
        ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
            Complex.phaseCutoffFrequencyTwistIntegrand
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ +
            ‖∫ x in (a : ℝ)..(b : ℝ),
              Complex.realPhaseOscillation
                (Complex.realPhaseFrequencyTwist
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  0) x‖ +
            ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
              Complex.phaseCutoffFrequencyTwistIntegrand
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ =
          (‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
              Complex.phaseCutoffFrequencyTwistIntegrand
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ +
            ‖∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
              Complex.phaseCutoffFrequencyTwistIntegrand
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖) +
            ‖∫ x in (a : ℝ)..(b : ℝ),
              Complex.realPhaseOscillation
                (Complex.realPhaseFrequencyTwist
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  0) x‖ :=
      calc
        _ = _ := add_assoc _ _ _
        _ = _ := congrArg
          (fun value : ℝ =>
            ‖∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
                Complex.phaseCutoffFrequencyTwistIntegrand
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  (Real.quantitativeLogarithmicBlockCutoff a b) 0 x‖ + value)
          (add_comm _ _)
        _ = _ := (add_assoc _ _ _).symm
    exact
        Eq.subst
        (motive := fun left : ℝ =>
          left ≤ 2 / 3 +
            (2 * ((b : ℝ) / ‖t‖) + ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹))
        hreorder.symm
        hsum
  have hbound := le_trans htriangle hcomponents
  have hbound_reassociated :
      2 / 3 +
          (2 * ((b : ℝ) / ‖t‖) + ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹) =
        2 / 3 + 2 * ((b : ℝ) / ‖t‖) +
          ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ :=
    (add_assoc _ _ _).symm
  have hbound_target :
      ‖(∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) 0 x) +
        (∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              0) x) +
        (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.quantitativeLogarithmicBlockCutoff a b) 0 x)‖ ≤
      2 / 3 + 2 * ((b : ℝ) / ‖t‖) +
        ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹ :=
    Eq.subst hbound_reassociated hbound
  exact
    Eq.subst
      (motive := fun value : ℂ =>
        ‖value‖ ≤ 2 / 3 + 2 * ((b : ℝ) / ‖t‖) + ((b : ℝ) - (a : ℝ)) • ‖t‖⁻¹)
      hdecomposition.symm
      hbound_target

theorem Complex.realPhaseOscillation_logarithmicFrequencyZero_eq
    (t : ℝ)
    (x : ℝ) :
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        0) x =
      Complex.realPhaseOscillation
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x := by
  exact
    congrArg
      (fun value : ℝ => Complex.realPhaseOscillation
        (fun _ : ℝ => value) x)
      (Complex.realPhaseFrequencyTwist_zero
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x)

end
end LFunctions
end Boundary
