import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSharpSupportRatios

/-!
# Curvature coefficients relative to the endpoint frequency shift

This owner converts support comparability into the exact powers of the
positive endpoint shift needed by the shifted-series absorption theorem.  The
three estimates correspond to the curvature-cubic, third-derivative-cubic,
and curvature-square-fourth terms of the phase-adapted packet majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.square_le_square_of_nonneg
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hmul := mul_self_le_mul_self hx hxy
  exact le_trans (le_of_eq (pow_two x))
    (le_trans hmul (le_of_eq (pow_two y).symm))

theorem Real.cube_le_cube_of_nonneg
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 3 ≤ y ^ 3 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hsquare := Real.square_le_square_of_nonneg hx hxy
  have hmul := mul_le_mul hsquare hxy hx (pow_nonneg hy 2)
  have hleft : x ^ 3 = x ^ 2 * x := pow_succ x 2
  have hright : y ^ 2 * y = y ^ 3 := (pow_succ y 2).symm
  exact le_trans (le_of_eq hleft)
    (le_trans hmul (le_of_eq hright))

theorem Real.square_mul_square
    (x y : ℝ) :
    (x * y) ^ 2 = x ^ 2 * y ^ 2 := by
  exact mul_pow x y 2

theorem Real.cube_mul_cube
    (x y : ℝ) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 := by
  exact mul_pow x y 3

theorem Real.norm_le_norm_square
    {T : ℝ} (hT : 1 ≤ T) :
    T ≤ T ^ 2 := by
  have hTNonneg : 0 ≤ T := le_trans zero_le_one hT
  have hmul := mul_le_mul_of_nonneg_left hT hTNonneg
  exact le_trans (le_of_eq (mul_one T).symm)
    (le_trans hmul (le_of_eq (pow_two T).symm))

theorem Real.norm_square_le_norm_cube
    {T : ℝ} (hT : 1 ≤ T) :
    T ^ 2 ≤ T ^ 3 := by
  have hTSquareNonneg : 0 ≤ T ^ 2 := sq_nonneg T
  have hmul := mul_le_mul_of_nonneg_left hT hTSquareNonneg
  exact le_trans (le_of_eq (mul_one (T ^ 2)).symm)
    (Eq.subst (pow_succ T 2).symm hmul)

theorem Real.ratio_square_bound
    {left right q : ℝ}
    (hleft : 0 < left)
    (hq : 0 ≤ q)
    (hright : right ≤ q * left)
    (hrightNonneg : 0 ≤ right) :
    right ^ 2 ≤ q ^ 2 * left ^ 2 := by
  have hscaledNonneg : 0 ≤ q * left :=
    mul_nonneg hq hleft.le
  have hsquare := Real.square_le_square_of_nonneg
    hrightNonneg hright
  exact le_trans hsquare
    (le_of_eq (Real.square_mul_square q left))

theorem Real.ratio_cube_bound
    {left right q : ℝ}
    (hleft : 0 < left)
    (hq : 0 ≤ q)
    (hright : right ≤ q * left)
    (hrightNonneg : 0 ≤ right) :
    right ^ 3 ≤ q ^ 3 * left ^ 3 := by
  have hscaledNonneg : 0 ≤ q * left :=
    mul_nonneg hq hleft.le
  have hcube := Real.cube_le_cube_of_nonneg
    hrightNonneg hright
  exact le_trans hcube
    (le_of_eq (Real.cube_mul_cube q left))

theorem Real.curvature_div_left_sq_le_ratio_sq_shift_sq
    {T left right q : ℝ}
    (hT : 1 ≤ T)
    (hleft : 0 < left)
    (hright : 0 < right)
    (hq : 0 ≤ q)
    (hratio : right ≤ q * left) :
    T / left ^ 2 ≤
      q ^ 2 * (T / right) ^ 2 := by
  have hleftSquare : 0 < left ^ 2 := pow_pos hleft 2
  have hrightSquare : 0 < right ^ 2 := pow_pos hright 2
  have hratioSquare := Real.ratio_square_bound
    hleft hq hratio hright.le
  have hTNonneg : 0 ≤ T := le_trans zero_le_one hT
  have hTLeSquare := Real.norm_le_norm_square hT
  have hfirst := mul_le_mul_of_nonneg_left hratioSquare hTNonneg
  have hqSquareNonneg : 0 ≤ q ^ 2 := sq_nonneg q
  have hleftSquareNonneg : 0 ≤ left ^ 2 := sq_nonneg left
  have hcross :
      T * right ^ 2 ≤ q ^ 2 * T ^ 2 * left ^ 2 := by
    have hsecondReassociate :
        T ^ 2 * (q ^ 2 * left ^ 2) = q ^ 2 * T ^ 2 * left ^ 2 := by
      exact Eq.trans (mul_assoc (T ^ 2) (q ^ 2) (left ^ 2)).symm
        (congrArg (fun value : ℝ => value * left ^ 2)
          (mul_comm (T ^ 2) (q ^ 2)))
    have hmiddle : T * right ^ 2 ≤ T * (q ^ 2 * left ^ 2) := hfirst
    have hraise : T * (q ^ 2 * left ^ 2) ≤
        T ^ 2 * (q ^ 2 * left ^ 2) := by
      exact mul_le_mul_of_nonneg_right hTLeSquare
        (mul_nonneg hqSquareNonneg hleftSquareNonneg)
    exact le_trans hmiddle
      (le_trans hraise (le_of_eq hsecondReassociate))
  have hdivision :
      T / left ^ 2 ≤ (q ^ 2 * T ^ 2) / right ^ 2 :=
    (div_le_div_iff₀ hleftSquare hrightSquare).mpr hcross
  have hrightNormalize :
      (q ^ 2 * T ^ 2) / right ^ 2 =
        q ^ 2 * (T / right) ^ 2 := by
    have hdivSquare : (T / right) ^ 2 = T ^ 2 / right ^ 2 :=
      div_pow T right 2
    exact Eq.trans (mul_div_assoc (q ^ 2) (T ^ 2) (right ^ 2))
      (congrArg (fun value : ℝ => q ^ 2 * value) hdivSquare.symm)
  exact le_trans hdivision (le_of_eq hrightNormalize)

theorem Real.third_coefficient_le_ratio_shift_sq
    {T left right length q s : ℝ}
    (hT : 1 ≤ T)
    (hleft : 0 < left)
    (hright : 0 < right)
    (hlength : 0 ≤ length)
    (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hratio : right ≤ q * left)
    (hlengthRatio : length ≤ s * left) :
    length * (2 * T / left ^ 3) ≤
      (2 * s * q ^ 2) * (T / right) ^ 2 := by
  have hcurvature := Real.curvature_div_left_sq_le_ratio_sq_shift_sq
    hT hleft hright hq hratio
  have hleftInv : length / left ≤ s := by
    exact (div_le_iff₀ hleft).mpr hlengthRatio
  have hleftInvNonneg : 0 ≤ length / left :=
    div_nonneg hlength hleft.le
  have htwoNonneg : 0 ≤ (2 : ℝ) := zero_le_two
  have hfactor : 2 * (length / left) ≤ 2 * s :=
    mul_le_mul_of_nonneg_left hleftInv htwoNonneg
  have hcurvatureNonneg : 0 ≤ T / left ^ 2 :=
    div_nonneg (le_trans zero_le_one hT) (pow_nonneg hleft.le 2)
  have hfactorNonneg : 0 ≤ 2 * (length / left) :=
    mul_nonneg htwoNonneg hleftInvNonneg
  have htargetFactorNonneg : 0 ≤ 2 * s :=
    mul_nonneg htwoNonneg hs
  have hproduct := mul_le_mul hfactor hcurvature
    hcurvatureNonneg htargetFactorNonneg
  have hleftNormalize :
      2 * (length / left) * (T / left ^ 2) =
        length * (2 * T / left ^ 3) := by
    have htwoLength : 2 * (length / left) = (2 * length) / left :=
      (mul_div_assoc 2 length left).symm
    have hcube : left ^ 3 = left * left ^ 2 := pow_succ' left 2
    have hnumerator : (2 * length) * T = length * (2 * T) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * T) (mul_comm 2 length))
        (mul_assoc length 2 T)
    calc
      2 * (length / left) * (T / left ^ 2) =
          ((2 * length) / left) * (T / left ^ 2) :=
        congrArg (fun value : ℝ => value * (T / left ^ 2)) htwoLength
      _ = ((2 * length) * T) / (left * left ^ 2) :=
        div_mul_div_comm (2 * length) left T (left ^ 2)
      _ = (length * (2 * T)) / left ^ 3 :=
        congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
          hnumerator hcube.symm
      _ = length * (2 * T / left ^ 3) :=
        mul_div_assoc length (2 * T) (left ^ 3)
  have hrightNormalize :
      2 * s * (q ^ 2 * (T / right) ^ 2) =
        (2 * s * q ^ 2) * (T / right) ^ 2 :=
    (mul_assoc (2 * s) (q ^ 2) ((T / right) ^ 2)).symm
  exact le_trans (le_of_eq hleftNormalize.symm)
    (le_trans hproduct (le_of_eq hrightNormalize))

theorem Real.fourth_coefficient_le_ratio_shift_cube
    {T left right length q s : ℝ}
    (hT : 1 ≤ T)
    (hleft : 0 < left)
    (hright : 0 < right)
    (hlength : 0 ≤ length)
    (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hratio : right ≤ q * left)
    (hlengthRatio : length ≤ s * left) :
    3 * length * (T / left ^ 2) ^ 2 ≤
      (3 * s * q ^ 3) * (T / right) ^ 3 := by
  have hratioCube := Real.ratio_cube_bound
    hleft hq hratio hright.le
  have hlengthScaledRaw := mul_le_mul_of_nonneg_left
    hlengthRatio (Nat.cast_nonneg 3)
  have hlengthScaled : 3 * length ≤ 3 * s * left :=
    le_trans hlengthScaledRaw (le_of_eq (mul_assoc 3 s left).symm)
  have hTLeCube := Real.norm_square_le_norm_cube hT
  have hleftPos := pow_pos hleft 4
  have hrightPos := pow_pos hright 3
  have hcoarseNonneg : 0 ≤ 3 * length :=
    mul_nonneg (Nat.cast_nonneg 3) hlength
  have htargetCoefficient : 0 ≤ 3 * s * q ^ 3 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg 3) hs) (pow_nonneg hq 3)
  have hcrossBase :
      3 * length * T ^ 2 * right ^ 3 ≤
        3 * s * q ^ 3 * T ^ 3 * left ^ 4 := by
    have hfirstProduct :
        (3 * length) * right ^ 3 ≤
          (3 * s * left) * (q ^ 3 * left ^ 3) :=
      mul_le_mul hlengthScaled hratioCube
        (pow_nonneg hright.le 3)
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg 3) hs) hleft.le)
    have hproductNonneg :
        0 ≤ (3 * s * left) * (q ^ 3 * left ^ 3) :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (Nat.cast_nonneg 3) hs) hleft.le)
        (mul_nonneg (pow_nonneg hq 3) (pow_nonneg hleft.le 3))
    have hcombined :
        ((3 * length) * right ^ 3) * T ^ 2 ≤
          ((3 * s * left) * (q ^ 3 * left ^ 3)) * T ^ 3 :=
      mul_le_mul hfirstProduct hTLeCube (sq_nonneg T) hproductNonneg
    have hleftNormalize :
        3 * length * T ^ 2 * right ^ 3 =
          ((3 * length) * right ^ 3) * T ^ 2 := by
      exact Eq.trans (mul_assoc (3 * length) (T ^ 2) (right ^ 3))
        (Eq.trans
          (congrArg (fun value : ℝ => (3 * length) * value)
            (mul_comm (T ^ 2) (right ^ 3)))
          (mul_assoc (3 * length) (right ^ 3) (T ^ 2)).symm)
    have hleftFourth : left ^ 4 = left * left ^ 3 := pow_succ' left 3
    have hcoefficientNormalize :
        (3 * s * left) * (q ^ 3 * left ^ 3) =
          (3 * s * q ^ 3) * left ^ 4 := by
      calc
        (3 * s * left) * (q ^ 3 * left ^ 3) =
            ((3 * s * left) * q ^ 3) * left ^ 3 :=
          (mul_assoc (3 * s * left) (q ^ 3) (left ^ 3)).symm
        _ = ((3 * s * q ^ 3) * left) * left ^ 3 :=
          congrArg (fun value : ℝ => value * left ^ 3)
            (Eq.trans (mul_assoc (3 * s) left (q ^ 3))
              (Eq.trans
                (congrArg (fun value : ℝ => (3 * s) * value)
                  (mul_comm left (q ^ 3)))
                (mul_assoc (3 * s) (q ^ 3) left).symm))
        _ = (3 * s * q ^ 3) * (left * left ^ 3) :=
          mul_assoc (3 * s * q ^ 3) left (left ^ 3)
        _ = (3 * s * q ^ 3) * left ^ 4 :=
          congrArg (fun value : ℝ => (3 * s * q ^ 3) * value)
            hleftFourth.symm
    have hrightNormalize :
        ((3 * s * left) * (q ^ 3 * left ^ 3)) * T ^ 3 =
          3 * s * q ^ 3 * T ^ 3 * left ^ 4 := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * T ^ 3) hcoefficientNormalize)
        (Eq.trans
          (mul_assoc (3 * s * q ^ 3) (left ^ 4) (T ^ 3))
          (Eq.trans
            (congrArg (fun value : ℝ => (3 * s * q ^ 3) * value)
              (mul_comm (left ^ 4) (T ^ 3)))
            (mul_assoc (3 * s * q ^ 3) (T ^ 3) (left ^ 4)).symm))
    exact le_trans (le_of_eq hleftNormalize)
      (le_trans hcombined (le_of_eq hrightNormalize))
  have hleftDenominator : 0 < left ^ 4 := pow_pos hleft 4
  have hrightDenominator : 0 < right ^ 3 := pow_pos hright 3
  have hdivision :
      (3 * length * T ^ 2) / left ^ 4 ≤
        (3 * s * q ^ 3 * T ^ 3) / right ^ 3 :=
    (div_le_div_iff₀ hleftDenominator hrightDenominator).mpr hcrossBase
  have hleftNormalize :
      3 * length * (T / left ^ 2) ^ 2 =
        (3 * length * T ^ 2) / left ^ 4 := by
    have hdiv := div_pow T (left ^ 2) 2
    have hpow : (left ^ 2) ^ 2 = left ^ 4 :=
      Eq.trans (pow_mul left 2 2).symm
        (congrArg (fun exponent : ℕ => left ^ exponent)
          (show 2 * 2 = 4 from rfl))
    exact Eq.trans
      (congrArg (fun value : ℝ => 3 * length * value) hdiv)
      (Eq.trans (mul_div_assoc (3 * length) (T ^ 2) ((left ^ 2) ^ 2)).symm
        (congrArg (fun denominator : ℝ =>
          (3 * length * T ^ 2) / denominator) hpow))
  have hrightNormalize :
      (3 * s * q ^ 3) * (T / right) ^ 3 =
        (3 * s * q ^ 3 * T ^ 3) / right ^ 3 := by
    have hdiv := div_pow T right 3
    exact Eq.trans
      (congrArg (fun value : ℝ => (3 * s * q ^ 3) * value) hdiv)
      (mul_div_assoc (3 * s * q ^ 3) (T ^ 3) (right ^ 3)).symm
  exact le_trans (le_of_eq hleftNormalize)
    (le_trans hdivision (le_of_eq hrightNormalize.symm))

end
end LFunctions
end Boundary
