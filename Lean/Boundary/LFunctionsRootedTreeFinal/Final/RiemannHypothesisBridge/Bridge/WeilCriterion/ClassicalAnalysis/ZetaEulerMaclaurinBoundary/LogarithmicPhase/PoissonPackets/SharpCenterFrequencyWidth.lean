import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CenterFrequencyWidth

/-!
# Sharp center-to-frequency width transport

The coarse width lemma bounds the angular coefficient `‖t‖/(2π)` by `‖t‖`.
Endpoint packing needs the retained `2π`.  This owner records the exact
reciprocal-difference formula and transports it to a square-denominator bound
without discarding the angular normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.mul_div_mul_div_eq_mul_div_mul
    (x gap angular denominator : ℝ) :
    (x / angular) * (gap / denominator) =
      x * gap / (angular * denominator) := by
  calc
    (x / angular) * (gap / denominator) =
        (x * gap) / (angular * denominator) := by
      exact div_mul_div_comm x angular gap denominator
    _ = x * gap / (angular * denominator) := rfl

theorem Real.mul_le_mul_div_of_denominator_le
    {coefficient gap first second : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hgap : 0 ≤ gap)
    (hfirst : 0 < first)
    (hdenominator : first ≤ second) :
    coefficient * gap / second ≤ coefficient * gap / first := by
  have hnumerator : 0 ≤ coefficient * gap :=
    mul_nonneg hcoefficient hgap
  exact div_le_div_of_nonneg_left hnumerator hfirst hdenominator

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_eq_angular_gap
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hright : 0 < right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right =
      ‖t‖ * (right - left) /
        ((2 * Real.pi) * (left * right)) := by
  have hexact :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_sub
      t left right (ne_of_gt hleft) (ne_of_gt hright)
  have hnormalize :
      (‖t‖ / (2 * Real.pi)) * ((right - left) / (left * right)) =
        ‖t‖ * (right - left) /
          ((2 * Real.pi) * (left * right)) :=
    Real.mul_div_mul_div_eq_mul_div_mul
      ‖t‖ (right - left) (2 * Real.pi) (left * right)
  exact hexact.trans hnormalize

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_le_angular_left_sq
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤
      ‖t‖ * (right - left) /
        ((2 * Real.pi) * left ^ 2) := by
  have hright : 0 < right := lt_of_lt_of_le hleft hleftRight
  have hgapNonneg : 0 ≤ right - left := sub_nonneg.mpr hleftRight
  have hleftProduct : left ^ 2 ≤ left * right := by
    have hscaled := mul_le_mul_of_nonneg_left hleftRight hleft.le
    exact Eq.subst
      (motive := fun value : ℝ => value ≤ left * right)
      (pow_two left).symm hscaled
  have hangularNonneg : 0 ≤ 2 * Real.pi :=
    Real.two_mul_pi_pos_explicit.le
  have hdenominator :
      (2 * Real.pi) * left ^ 2 ≤
        (2 * Real.pi) * (left * right) :=
    mul_le_mul_of_nonneg_left hleftProduct hangularNonneg
  have hleftDenominator : 0 < (2 * Real.pi) * left ^ 2 :=
    mul_pos Real.two_mul_pi_pos_explicit (sq_pos_of_pos hleft)
  have hnumerator : 0 ≤ ‖t‖ * (right - left) :=
    mul_nonneg (norm_nonneg t) hgapNonneg
  have hratio :
      ‖t‖ * (right - left) /
          ((2 * Real.pi) * (left * right)) ≤
        ‖t‖ * (right - left) /
          ((2 * Real.pi) * left ^ 2) :=
    div_le_div_of_nonneg_left hnumerator hleftDenominator hdenominator
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ ‖t‖ * (right - left) /
        ((2 * Real.pi) * left ^ 2))
    (Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_eq_angular_gap
      t hleft hright).symm
    hratio

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_lt_one_of_angular
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right)
    (hangular :
      ‖t‖ * (right - left) < (2 * Real.pi) * left ^ 2) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right < 1 := by
  have hdenominatorPos : 0 < (2 * Real.pi) * left ^ 2 :=
    mul_pos Real.two_mul_pi_pos_explicit (sq_pos_of_pos hleft)
  have hratio :
      ‖t‖ * (right - left) /
          ((2 * Real.pi) * left ^ 2) < 1 :=
    (div_lt_one hdenominatorPos).mpr hangular
  exact lt_of_le_of_lt
    (Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_le_angular_left_sq
      t hleft hleftRight)
    hratio

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_le_angular_exact_product
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤
      ‖t‖ * (right - left) /
        ((2 * Real.pi) * (left * right)) := by
  have hright : 0 < right := lt_of_lt_of_le hleft hleftRight
  exact le_of_eq
    (Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_eq_angular_gap
      t hleft hright)

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_lt_one_of_product
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right)
    (hangular :
      ‖t‖ * (right - left) <
        (2 * Real.pi) * (left * right)) :
    Complex.logarithmicPhaseCenterFrequencyCoordinate t left -
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right < 1 := by
  have hright : 0 < right := lt_of_lt_of_le hleft hleftRight
  have hproductPos : 0 < left * right := mul_pos hleft hright
  have hdenominatorPos :
      0 < (2 * Real.pi) * (left * right) :=
    mul_pos Real.two_mul_pi_pos_explicit hproductPos
  have hratio :
      ‖t‖ * (right - left) /
          ((2 * Real.pi) * (left * right)) < 1 :=
    (div_lt_one hdenominatorPos).mpr hangular
  exact Eq.subst
    (motive := fun value : ℝ => value < 1)
    (Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_eq_angular_gap
      t hleft hright).symm
    hratio

theorem Complex.logarithmicPhaseCenterFrequencyCoordinate_reflected_width_lt_one
    (t : ℝ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right)
    (hangular :
      ‖t‖ * (right - left) < (2 * Real.pi) * left ^ 2) :
    (-Complex.logarithmicPhaseCenterFrequencyCoordinate t right) -
        (-Complex.logarithmicPhaseCenterFrequencyCoordinate t left) < 1 := by
  have hreflect := Real.reflected_interval_width
    (Complex.logarithmicPhaseCenterFrequencyCoordinate t right)
    (Complex.logarithmicPhaseCenterFrequencyCoordinate t left)
  have hwidth :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_sub_lt_one_of_angular
      t hleft hleftRight hangular
  exact Eq.subst
    (motive := fun value : ℝ => value < 1)
    hreflect.symm hwidth

theorem Complex.integerModeFamily_card_le_one_of_center_bounds
    (t : ℝ) (M : Finset ℤ) {left right : ℝ}
    (hleft : 0 < left) (hleftRight : left ≤ right)
    (hangular :
      ‖t‖ * (right - left) < (2 * Real.pi) * left ^ 2)
    (hcenters :
      ∀ m ∈ M,
        Complex.logarithmicPhaseCenterFrequencyCoordinate t right ≤ -(m : ℝ) ∧
          -(m : ℝ) ≤
            Complex.logarithmicPhaseCenterFrequencyCoordinate t left) :
    M.card ≤ 1 := by
  let lower := -Complex.logarithmicPhaseCenterFrequencyCoordinate t left
  let upper := -Complex.logarithmicPhaseCenterFrequencyCoordinate t right
  have hwidth : upper - lower < 1 :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_reflected_width_lt_one
      t hleft hleftRight hangular
  exact Finset.card_le_one_of_cast_mem_short_interval
    M hwidth (fun m hm =>
      (Int.neg_cast_mem_interval_iff_cast_mem_reflected_interval).mp
        (hcenters m hm))

end

end LFunctions
end Boundary
