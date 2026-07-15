import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.IntegerIntervalPacking
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessEndpointBudget

/-!
# Transport between logarithmic stationary centers and integer frequencies

For a negative integer mode `m`, the corrected stationary equation gives

`-(m : ℝ) = ‖t‖ / (2π x_m)`.

This owner proves the exact identity and its monotone endpoint transports.
These are the bridge from geometric endpoint layers in center space to short
real intervals containing the integer coordinate `-m`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseCenterFrequencyCoordinate
    (t x : ℝ) : ℝ :=
  ‖t‖ / (2 * Real.pi * x)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_eq
    (t x : ℝ) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t x =
      ‖t‖ / (2 * Real.pi * x) :=
  rfl

theorem Complex.logarithmicPhase_negativeModeCast_eq_centerFrequencyCoordinate
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    -(m : ℝ) =
      Complex.logarithmicPhaseCenterFrequencyCoordinate t
        (Complex.logarithmicPhaseFourierStationaryPoint t m) := by
  have htPos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hmCast : (m : ℝ) < 0 :=
    Eq.subst
      (motive := fun value : ℝ => (m : ℝ) < value)
      Int.cast_zero
      (Int.cast_lt.mpr hm)
  have hnegativeModePos : 0 < -(m : ℝ) :=
    neg_pos.mpr hmCast
  have htwoPiPos : 0 < (2 * Real.pi : ℝ) :=
    mul_pos zero_lt_two Real.pi_pos
  have htwoPiNe : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt htwoPiPos
  have hscaledCenter :
      2 * Real.pi *
          Complex.logarithmicPhaseFourierStationaryPoint t m =
        ‖t‖ / (-(m : ℝ)) := by
    unfold Complex.logarithmicPhaseFourierStationaryPoint
    calc
      2 * Real.pi * (‖t‖ / (2 * Real.pi * (-(m : ℝ)))) =
          (2 * Real.pi * ‖t‖) / (2 * Real.pi * (-(m : ℝ))) :=
        (mul_div_assoc (2 * Real.pi) ‖t‖
          (2 * Real.pi * (-(m : ℝ)))).symm
      _ = ‖t‖ / (-(m : ℝ)) :=
        mul_div_mul_left ‖t‖ (-(m : ℝ)) htwoPiNe
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have hcoordinateTransport :
      ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseFourierStationaryPoint t m) =
        ‖t‖ / (‖t‖ / (-(m : ℝ))) :=
    congrArg (fun denominator : ℝ => ‖t‖ / denominator)
      hscaledCenter
  have hreciprocal :
      ‖t‖ / (‖t‖ / (-(m : ℝ))) = -(m : ℝ) :=
    Real.logarithmicPhase_fourier_reciprocal_identity
      htPos hnegativeModePos
  exact (hcoordinateTransport.trans hreciprocal).symm

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_nonneg
    (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ Complex.logarithmicPhaseCenterFrequencyCoordinate t x := by
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have htwoPiPos : 0 < (2 * Real.pi : ℝ) :=
    mul_pos zero_lt_two Real.pi_pos
  exact div_nonneg (norm_nonneg t)
    (mul_nonneg htwoPiPos.le hx)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_antitone
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤
      Complex.logarithmicPhaseCenterFrequencyCoordinate t left := by
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have htwoPiPos : 0 < (2 * Real.pi : ℝ) :=
    mul_pos zero_lt_two Real.pi_pos
  have htwoPiNonneg : 0 ≤ 2 * Real.pi := htwoPiPos.le
  have hdenominator := mul_le_mul_of_nonneg_left hleftRight htwoPiNonneg
  have hleftDenominator : 0 < 2 * Real.pi * left :=
    mul_pos htwoPiPos hleft
  exact div_le_div_of_nonneg_left
    (norm_nonneg t) hleftDenominator hdenominator

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_strictAnti
    (t : ℝ) (ht : 1 ≤ ‖t‖) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left < right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t right <
      Complex.logarithmicPhaseCenterFrequencyCoordinate t left := by
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have hnormPos : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have htwoPiPos : 0 < (2 * Real.pi : ℝ) :=
    mul_pos zero_lt_two Real.pi_pos
  have hdenominator : 2 * Real.pi * left < 2 * Real.pi * right :=
    mul_lt_mul_of_pos_left hleftRight htwoPiPos
  have hleftDenominator : 0 < 2 * Real.pi * left :=
    mul_pos htwoPiPos hleft
  exact div_lt_div_of_pos_left hnormPos hleftDenominator hdenominator

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    {left right : ℝ}
    (hleft : 0 < left)
    (hcenter : left ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hright :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseCenterFrequencyCoordinate t left := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hleftToCenter :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_antitone
      t hleft hcenter
  have hcenterToRight :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_antitone
      t hcenterPos hright
  have hmode :=
    Complex.logarithmicPhase_negativeModeCast_eq_centerFrequencyCoordinate
      t ht hm
  exact And.intro
    (le_trans hcenterToRight (le_of_eq hmode.symm))
    (le_trans (le_of_eq hmode) hleftToCenter)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds_strict_left
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    {left right : ℝ}
    (hleft : 0 < left)
    (hcenter : left <
      Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hright :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseCenterFrequencyCoordinate t left := by
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
      t ht hm hleft hcenter.le hright

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds_strict_right
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0)
    {left right : ℝ}
    (hleft : 0 < left)
    (hcenter : left ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m)
    (hright :
      Complex.logarithmicPhaseFourierStationaryPoint t m < right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤ -(m : ℝ) ∧
      -(m : ℝ) ≤
        Complex.logarithmicPhaseCenterFrequencyCoordinate t left := by
  exact
    Complex.logarithmicPhaseCenterFrequencyCoordinate_bounds
      t ht hm hleft hcenter hright.le

theorem Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval
    {left right : ℝ} {m : ℤ} :
    left ≤ -(m : ℝ) ∧ -(m : ℝ) ≤ right ↔
      -right ≤ (m : ℝ) ∧ (m : ℝ) ≤ -left := by
  constructor
  · intro h
    have hmode : -(-(m : ℝ)) = (m : ℝ) :=
      neg_neg (m : ℝ)
    have hleftRaw : -right ≤ -(-(m : ℝ)) :=
      neg_le_neg h.2
    have hrightRaw : -(-(m : ℝ)) ≤ -left :=
      neg_le_neg h.1
    have hleftTransport : -right ≤ (m : ℝ) :=
      Eq.mp (congrArg (fun value : ℝ => -right ≤ value) hmode)
        hleftRaw
    have hrightTransport : (m : ℝ) ≤ -left :=
      Eq.mp (congrArg (fun value : ℝ => value ≤ -left) hmode)
        hrightRaw
    exact And.intro
      hleftTransport
      hrightTransport
  · intro h
    have hleftRaw : -(-left) ≤ -(m : ℝ) :=
      neg_le_neg h.2
    have hrightRaw : -(m : ℝ) ≤ -(-right) :=
      neg_le_neg h.1
    have hleftTransport : left ≤ -(m : ℝ) :=
      Eq.mp
        (congrArg (fun value : ℝ => value ≤ -(m : ℝ))
          (neg_neg left))
        hleftRaw
    have hrightTransport : -(m : ℝ) ≤ right :=
      Eq.mp
        (congrArg (fun value : ℝ => -(m : ℝ) ≤ value)
          (neg_neg right))
        hrightRaw
    exact And.intro
      hleftTransport
      hrightTransport

theorem Real.reflected_interval_width
    (left right : ℝ) :
    (-left) - (-right) = right - left := by
  calc
    (-left) - (-right) = -left + right :=
      (sub_neg_eq_add (-left) right)
    _ = right + -left := add_comm _ _
    _ = right - left := (sub_eq_add_neg right left).symm

end

end LFunctions
end Boundary
