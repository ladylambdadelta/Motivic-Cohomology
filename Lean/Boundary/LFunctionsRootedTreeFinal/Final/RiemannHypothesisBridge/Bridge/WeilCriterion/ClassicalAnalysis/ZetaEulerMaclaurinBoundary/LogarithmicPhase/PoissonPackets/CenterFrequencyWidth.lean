import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessEndpointFrequencyLayers

/-!
# Width of a logarithmic center-frequency interval

The reciprocal center-frequency coordinate has an exact two-endpoint
difference formula.  This owner isolates that algebra and provides monotone
upper bounds suitable for endpoint layers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.inv_sub_inv
    (left right : ℝ)
    (hleft : left ≠ 0)
    (hright : right ≠ 0) :
    left⁻¹ - right⁻¹ = (right - left) / (left * right) := by
  have hproduct : left * right ≠ 0 := mul_ne_zero hleft hright
  have hleftForm :
      left⁻¹ = right / (left * right) := by
    have hcancel : right / (left * right) = left⁻¹ := by
      calc
        right / (left * right) = right * (left * right)⁻¹ :=
          div_eq_mul_inv right (left * right)
        _ = right * (right⁻¹ * left⁻¹) := by
          exact congrArg (fun value : ℝ => right * value)
            (mul_inv_rev left right)
        _ = (right * right⁻¹) * left⁻¹ :=
          (mul_assoc right right⁻¹ left⁻¹).symm
        _ = 1 * left⁻¹ := by
          exact congrArg (fun value : ℝ => value * left⁻¹)
            (mul_inv_cancel₀ hright)
        _ = left⁻¹ := one_mul _
    exact hcancel.symm
  have hrightForm :
      right⁻¹ = left / (left * right) := by
    have hcancel : left / (left * right) = right⁻¹ := by
      calc
        left / (left * right) = left * (left * right)⁻¹ :=
          div_eq_mul_inv left (left * right)
        _ = left * (right⁻¹ * left⁻¹) := by
          exact congrArg (fun value : ℝ => left * value)
            (mul_inv_rev left right)
        _ = left * (left⁻¹ * right⁻¹) := by
          exact congrArg (fun value : ℝ => left * value)
            (mul_comm right⁻¹ left⁻¹)
        _ = (left * left⁻¹) * right⁻¹ :=
          (mul_assoc left left⁻¹ right⁻¹).symm
        _ = 1 * right⁻¹ := by
          exact congrArg (fun value : ℝ => value * right⁻¹)
            (mul_inv_cancel₀ hleft)
        _ = right⁻¹ := one_mul _
    exact hcancel.symm
  calc
    left⁻¹ - right⁻¹ =
        right / (left * right) - left / (left * right) := by
      exact congrArg₂ (fun first second : ℝ => first - second)
        hleftForm hrightForm
    _ = (right - left) / (left * right) :=
      (sub_div right left (left * right)).symm

theorem Real.two_mul_pi_pos_explicit :
    0 < (2 : ℝ) * Real.pi :=
  mul_pos zero_lt_two Real.pi_pos

theorem Real.one_le_two_mul_pi_explicit :
    (1 : ℝ) ≤ 2 * Real.pi := by
  have honeLeTwo : (1 : ℝ) ≤ 2 := one_le_two
  have htwoLePi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
  have honeLePi : (1 : ℝ) ≤ Real.pi :=
    le_trans honeLeTwo htwoLePi
  have hpiNonneg : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hpiLeTwoPi : Real.pi ≤ 2 * Real.pi := by
    have hscaled : 1 * Real.pi ≤ 2 * Real.pi :=
      mul_le_mul_of_nonneg_right honeLeTwo hpiNonneg
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ 2 * Real.pi)
      (one_mul Real.pi)
      hscaled
  exact le_trans honeLePi hpiLeTwoPi

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_eq_norm_mul_inv
    (t x : ℝ) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t x =
      (‖t‖ / (2 * Real.pi)) * x⁻¹ := by
  unfold Complex.logarithmicPhaseCenterFrequencyCoordinate
  have htwoPiNe : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Real.two_mul_pi_pos_explicit
  calc
    ‖t‖ / (2 * Real.pi * x) =
        ‖t‖ * (2 * Real.pi * x)⁻¹ :=
      div_eq_mul_inv ‖t‖ (2 * Real.pi * x)
    _ = ‖t‖ * (x⁻¹ * (2 * Real.pi)⁻¹) := by
      exact congrArg (fun value : ℝ => ‖t‖ * value)
        (mul_inv_rev (2 * Real.pi) x)
    _ = (‖t‖ * (2 * Real.pi)⁻¹) * x⁻¹ := by
      calc
        ‖t‖ * (x⁻¹ * (2 * Real.pi)⁻¹) =
            ‖t‖ * ((2 * Real.pi)⁻¹ * x⁻¹) := by
          exact congrArg (fun value : ℝ => ‖t‖ * value)
            (mul_comm x⁻¹ (2 * Real.pi)⁻¹)
        _ = (‖t‖ * (2 * Real.pi)⁻¹) * x⁻¹ :=
          (mul_assoc ‖t‖ (2 * Real.pi)⁻¹ x⁻¹).symm
    _ = (‖t‖ / (2 * Real.pi)) * x⁻¹ := by
      exact congrArg (fun value : ℝ => value * x⁻¹)
        (div_eq_mul_inv ‖t‖ (2 * Real.pi)).symm

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub
    (t left right : ℝ)
    (hleft : left ≠ 0)
    (hright : right ≠ 0) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right =
      (‖t‖ / (2 * Real.pi)) *
        ((right - left) / (left * right)) := by
  have hleftForm :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_eq_norm_mul_inv t left
  have hrightForm :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_eq_norm_mul_inv t right
  calc
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right =
      (‖t‖ / (2 * Real.pi)) * left⁻¹ -
        (‖t‖ / (2 * Real.pi)) * right⁻¹ := by
      exact congrArg₂ (fun first second : ℝ => first - second)
        hleftForm hrightForm
    _ = (‖t‖ / (2 * Real.pi)) * (left⁻¹ - right⁻¹) :=
      (mul_sub (‖t‖ / (2 * Real.pi)) left⁻¹ right⁻¹).symm
    _ = (‖t‖ / (2 * Real.pi)) *
        ((right - left) / (left * right)) := by
      exact congrArg
        (fun value : ℝ => (‖t‖ / (2 * Real.pi)) * value)
        (Real.inv_sub_inv left right hleft hright)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_nonneg
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right) :
    0 ≤ Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
      Complex.logarithmicPhaseCenterFrequencyCoordinate t right := by
  exact sub_nonneg.mpr
    (Complex.logarithmicPhaseCenterFrequencyCoordinate_antitone
      t hleft hleftRight)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_le_norm_mul_gap_div_left_sq
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤
      ‖t‖ * (right - left) / left ^ 2 := by
  have hright : 0 < right := lt_of_lt_of_le hleft hleftRight
  have htwoPiOne : (1 : ℝ) ≤ 2 * Real.pi :=
    Real.one_le_two_mul_pi_explicit
  have htwoPiPos : (0 : ℝ) < 2 * Real.pi :=
    Real.two_mul_pi_pos_explicit
  have hfrequencyCoefficient :
      ‖t‖ / (2 * Real.pi) ≤ ‖t‖ := by
    have hscaled : ‖t‖ * 1 ≤ ‖t‖ * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left htwoPiOne (norm_nonneg t)
    have hnormLeScaled : ‖t‖ ≤ ‖t‖ * (2 * Real.pi) :=
      le_trans (le_of_eq (mul_one ‖t‖).symm) hscaled
    exact (div_le_iff₀ htwoPiPos).mpr hnormLeScaled
  have hgapNonneg : 0 ≤ right - left := sub_nonneg.mpr hleftRight
  have hleftRightProduct : left ^ 2 ≤ left * right := by
    have hscaled := mul_le_mul_of_nonneg_left hleftRight hleft.le
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ left * right)
      (pow_two left).symm hscaled
  have hleftSqPos : 0 < left ^ 2 := sq_pos_of_pos hleft
  have hratio :
      (right - left) / (left * right) ≤
        (right - left) / left ^ 2 := by
    exact div_le_div_of_nonneg_left
      hgapNonneg hleftSqPos hleftRightProduct
  have hfirst := mul_le_mul hfrequencyCoefficient hratio
    (div_nonneg hgapNonneg (mul_nonneg hleft.le hright.le))
    (norm_nonneg t)
  have hidentity :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_sub
      t left right (ne_of_gt hleft) (ne_of_gt hright)
  have hrightNormalize :
      ‖t‖ * ((right - left) / left ^ 2) =
        ‖t‖ * (right - left) / left ^ 2 :=
    (mul_div_assoc ‖t‖ (right - left) (left ^ 2)).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ ‖t‖ * (right - left) / left ^ 2)
    hidentity.symm
    (le_trans hfirst (le_of_eq hrightNormalize))

end

end LFunctions
end Boundary
