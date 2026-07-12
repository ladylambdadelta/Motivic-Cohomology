import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionReciprocalCoordinates

/-!
# Positivity of the transition curvature discriminant

After writing the reciprocal sum as `s=4+r`, the squared curvature comparison
has the polynomial shown below.  Its only negative coefficient is linear and
is absorbed separately on `0≤r≤1` and on `1≤r`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.transitionShiftedDiscriminant (r : ℝ) : ℝ :=
  16 - 16 * r + 188 * r ^ 2 + 224 * r ^ 3 +
    92 * r ^ 4 + 16 * r ^ 5 + r ^ 6

def Real.transitionCurvatureDiscriminant (s : ℝ) : ℝ :=
  Real.transitionShiftedDiscriminant (s - 4)

def Real.transitionCurvatureRawDiscriminant (s : ℝ) : ℝ :=
  (s ^ 3 - 4 * s ^ 2 + 4) ^ 2 -
    4 * (s - 1) ^ 2 * s * (s - 4)

theorem Real.transitionShiftedDiscriminant_eq_low_core_add_tail
    (r : ℝ) :
    Real.transitionShiftedDiscriminant r =
      (16 - 16 * r) +
        (188 * r ^ 2 + 224 * r ^ 3 +
          92 * r ^ 4 + 16 * r ^ 5 + r ^ 6) := by
  unfold Real.transitionShiftedDiscriminant
  exact
    (add_assoc
      (16 - 16 * r)
      (188 * r ^ 2)
      (224 * r ^ 3)).trans
      ((add_assoc
        ((16 - 16 * r) + 188 * r ^ 2)
        (224 * r ^ 3)
        (92 * r ^ 4)).trans
        ((add_assoc
          (((16 - 16 * r) + 188 * r ^ 2) + 224 * r ^ 3)
          (92 * r ^ 4)
          (16 * r ^ 5)).trans
          (add_assoc
            ((((16 - 16 * r) + 188 * r ^ 2) + 224 * r ^ 3) +
              92 * r ^ 4)
            (16 * r ^ 5)
            (r ^ 6))))

theorem Real.transitionShiftedDiscriminant_tail_nonneg
    {r : ℝ}
    (hr : 0 ≤ r) :
    0 ≤ 188 * r ^ 2 + 224 * r ^ 3 +
      92 * r ^ 4 + 16 * r ^ 5 + r ^ 6 := by
  have hr2 : 0 ≤ r ^ 2 := pow_nonneg r 2
  have hr3 : 0 ≤ r ^ 3 := pow_nonneg r 3
  have hr4 : 0 ≤ r ^ 4 := pow_nonneg r 4
  have hr5 : 0 ≤ r ^ 5 := pow_nonneg r 5
  have hr6 : 0 ≤ r ^ 6 := pow_nonneg r 6
  have h188 : 0 ≤ 188 * r ^ 2 :=
    mul_nonneg (Nat.cast_nonneg 188) hr2
  have h224 : 0 ≤ 224 * r ^ 3 :=
    mul_nonneg (Nat.cast_nonneg 224) hr3
  have h92 : 0 ≤ 92 * r ^ 4 :=
    mul_nonneg (Nat.cast_nonneg 92) hr4
  have h16 : 0 ≤ 16 * r ^ 5 :=
    mul_nonneg (Nat.cast_nonneg 16) hr5
  exact add_nonneg
    (add_nonneg (add_nonneg (add_nonneg h188 h224) h92) h16)
    hr6

theorem Real.transitionShiftedDiscriminant_low_core_nonneg
    {r : ℝ}
    (hr : 0 ≤ r)
    (hrOne : r ≤ 1) :
    0 ≤ 16 - 16 * r := by
  have hscaled : 16 * r ≤ 16 * 1 :=
    mul_le_mul_of_nonneg_left hrOne (Nat.cast_nonneg 16)
  have hright : (16 : ℝ) * 1 = 16 := mul_one 16
  exact sub_nonneg.mpr (le_trans hscaled (le_of_eq hright))

theorem Real.transitionShiftedDiscriminant_nonneg_of_le_one
    {r : ℝ}
    (hr : 0 ≤ r)
    (hrOne : r ≤ 1) :
    0 ≤ Real.transitionShiftedDiscriminant r := by
  have hcore :=
    Real.transitionShiftedDiscriminant_low_core_nonneg hr hrOne
  have htail := Real.transitionShiftedDiscriminant_tail_nonneg hr
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    (Real.transitionShiftedDiscriminant_eq_low_core_add_tail r).symm
    (add_nonneg hcore htail)

theorem Real.sixteen_r_le_one_eighty_eight_r_sq_of_one_le
    {r : ℝ}
    (hrOne : 1 ≤ r) :
    16 * r ≤ 188 * r ^ 2 := by
  have hr : 0 ≤ r := le_trans zero_le_one hrOne
  have hsixteenLe : (16 : ℝ) ≤ 188 := by
    have h172 : (0 : ℝ) ≤ 172 := Nat.cast_nonneg 172
    have hadd : (16 : ℝ) ≤ 16 + 172 :=
      le_add_of_nonneg_right h172
    have hsum : (16 : ℝ) + 172 = 188 := by
      exact Eq.trans
        (Nat.cast_add 16 172).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ))
            (show (16 + 172 : ℕ) = 188 from rfl))
          Nat.cast_ofNat)
    exact hadd.trans_eq hsum
  have hcoefficient : 16 * r ≤ 188 * r :=
    mul_le_mul_of_nonneg_right hsixteenLe hr
  have hrMul : 188 * r ≤ 188 * (r * r) := by
    have hrr : r ≤ r * r := by
      have hmul := mul_le_mul_of_nonneg_left hrOne hr
      exact le_trans (le_of_eq (mul_one r).symm) hmul
    exact mul_le_mul_of_nonneg_left hrr (Nat.cast_nonneg 188)
  have hsquare : r * r = r ^ 2 := (pow_two r).symm
  exact le_trans hcoefficient
    (le_trans hrMul
      (le_of_eq
        (congrArg (fun value : ℝ => 188 * value) hsquare)))

theorem Real.transitionShiftedDiscriminant_high_core_nonneg
    {r : ℝ}
    (hrOne : 1 ≤ r) :
    0 ≤ 16 - 16 * r + 188 * r ^ 2 := by
  have hdominates :=
    Real.sixteen_r_le_one_eighty_eight_r_sq_of_one_le hrOne
  have hdifference : 0 ≤ 188 * r ^ 2 - 16 * r :=
    sub_nonneg.mpr hdominates
  have hsixteen : (0 : ℝ) ≤ 16 := Nat.cast_nonneg 16
  have hreassociate :
      16 - 16 * r + 188 * r ^ 2 =
        16 + (188 * r ^ 2 - 16 * r) := by
    calc
      16 - 16 * r + 188 * r ^ 2 =
          (16 + -(16 * r)) + 188 * r ^ 2 :=
        congrArg (fun value : ℝ => value + 188 * r ^ 2)
          (sub_eq_add_neg 16 (16 * r))
      _ = 16 + (-(16 * r) + 188 * r ^ 2) :=
        add_assoc 16 (-(16 * r)) (188 * r ^ 2)
      _ = 16 + (188 * r ^ 2 + -(16 * r)) :=
        congrArg (fun value : ℝ => 16 + value)
          (add_comm (-(16 * r)) (188 * r ^ 2))
      _ = 16 + (188 * r ^ 2 - 16 * r) :=
        congrArg (fun value : ℝ => 16 + value)
          (sub_eq_add_neg (188 * r ^ 2) (16 * r)).symm
  exact Eq.subst
    (motive := fun value : ℝ => 0 ≤ value)
    hreassociate.symm
    (add_nonneg hsixteen hdifference)

theorem Real.transitionShiftedDiscriminant_nonneg_of_one_le
    {r : ℝ}
    (hrOne : 1 ≤ r) :
    0 ≤ Real.transitionShiftedDiscriminant r := by
  have hr : 0 ≤ r := le_trans zero_le_one hrOne
  have hcore :=
    Real.transitionShiftedDiscriminant_high_core_nonneg hrOne
  have h224 : 0 ≤ 224 * r ^ 3 :=
    mul_nonneg (Nat.cast_nonneg 224) (pow_nonneg r 3)
  have h92 : 0 ≤ 92 * r ^ 4 :=
    mul_nonneg (Nat.cast_nonneg 92) (pow_nonneg r 4)
  have h16 : 0 ≤ 16 * r ^ 5 :=
    mul_nonneg (Nat.cast_nonneg 16) (pow_nonneg r 5)
  have hr6 : 0 ≤ r ^ 6 := pow_nonneg r 6
  unfold Real.transitionShiftedDiscriminant
  exact add_nonneg
    (add_nonneg (add_nonneg (add_nonneg hcore h224) h92) h16)
    hr6

theorem Real.transitionShiftedDiscriminant_nonneg
    {r : ℝ}
    (hr : 0 ≤ r) :
    0 ≤ Real.transitionShiftedDiscriminant r := by
  match le_total r 1 with
  | Or.inl hrOne =>
      exact Real.transitionShiftedDiscriminant_nonneg_of_le_one hr hrOne
  | Or.inr hOneR =>
      exact Real.transitionShiftedDiscriminant_nonneg_of_one_le hOneR

theorem Real.transitionCurvatureDiscriminant_eq_shifted
    (s : ℝ) :
    Real.transitionCurvatureDiscriminant s =
      Real.transitionShiftedDiscriminant (s - 4) := by
  rfl

theorem Real.transitionCurvatureDiscriminant_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ Real.transitionCurvatureDiscriminant s := by
  have hshift : 0 ≤ s - 4 := sub_nonneg.mpr hs
  unfold Real.transitionCurvatureDiscriminant
  exact Real.transitionShiftedDiscriminant_nonneg hshift

theorem Real.transitionScalar_one_le
    {s : ℝ}
    (hs : 4 ≤ s) :
    1 ≤ s := by
  have honeLeFour : (1 : ℝ) ≤ 4 := by
    have hthreeNonneg : (0 : ℝ) ≤ 3 := Nat.cast_nonneg 3
    have hadd : (1 : ℝ) ≤ 1 + 3 := le_add_of_nonneg_right hthreeNonneg
    have hsum : (1 : ℝ) + 3 = 4 := by
      exact Eq.trans
        (Nat.cast_add 1 3).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ))
            (show (1 + 3 : ℕ) = 4 from rfl))
          Nat.cast_ofNat)
    exact hadd.trans_eq hsum
  exact le_trans honeLeFour hs

theorem Real.transitionScalar_two_le
    {s : ℝ}
    (hs : 4 ≤ s) :
    2 ≤ s := by
  have htwoLeFour : (2 : ℝ) ≤ 4 := by
    have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
    have hadd : (2 : ℝ) ≤ 2 + 2 := le_add_of_nonneg_right htwoNonneg
    have hsum : (2 : ℝ) + 2 = 4 := by
      exact Eq.trans
        (Nat.cast_add 2 2).symm
        (Eq.trans
          (congrArg (fun n : ℕ => (n : ℝ))
            (show (2 + 2 : ℕ) = 4 from rfl))
          Nat.cast_ofNat)
    exact hadd.trans_eq hsum
  exact le_trans htwoLeFour hs

theorem Real.transitionScalar_pos
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 < s := by
  exact lt_of_lt_of_le zero_lt_one
    (Real.transitionScalar_one_le hs)

theorem Real.transitionScalar_sub_one_pos
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 < s - 1 := by
  exact sub_pos.mpr
    (lt_of_lt_of_le zero_lt_one
      (Real.transitionScalar_one_le hs))

theorem Real.transitionScalar_sub_two_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ s - 2 := by
  exact sub_nonneg.mpr (Real.transitionScalar_two_le hs)

theorem Real.transitionScalar_sub_four_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ s - 4 := by
  exact sub_nonneg.mpr hs

theorem Real.transitionScalar_energy_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ s * (s - 2) := by
  exact mul_nonneg
    (le_of_lt (Real.transitionScalar_pos hs))
    (Real.transitionScalar_sub_two_nonneg hs)

theorem Real.transitionScalar_cubicSum_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ s * (s - 1) := by
  exact mul_nonneg
    (le_of_lt (Real.transitionScalar_pos hs))
    (le_of_lt (Real.transitionScalar_sub_one_pos hs))

theorem Real.transitionScalar_gapSquare_nonneg
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 ≤ s * (s - 4) := by
  exact mul_nonneg
    (le_of_lt (Real.transitionScalar_pos hs))
    (Real.transitionScalar_sub_four_nonneg hs)

theorem Real.transitionScalar_denominator_pos
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 < 2 * (s - 1) := by
  exact mul_pos zero_lt_two
    (Real.transitionScalar_sub_one_pos hs)

theorem Real.transitionScalar_squaredEnergy_pos
    {s : ℝ}
    (hs : 4 ≤ s) :
    0 < (s * (s - 2)) ^ 2 := by
  have hsPos := Real.transitionScalar_pos hs
  have hsubPos : 0 < s - 2 := by
    have htwoLtFour : (2 : ℝ) < 4 := by
      have htwoPos : (0 : ℝ) < 2 := zero_lt_two
      have hadd : (2 : ℝ) < 2 + 2 := lt_add_of_pos_right 2 htwoPos
      have hsum : (2 : ℝ) + 2 = 4 := by
        exact Eq.trans
          (Nat.cast_add 2 2).symm
          (Eq.trans
            (congrArg (fun n : ℕ => (n : ℝ))
              (show (2 + 2 : ℕ) = 4 from rfl))
            Nat.cast_ofNat)
      exact hadd.trans_eq hsum
    exact sub_pos.mpr (lt_of_lt_of_le htwoLtFour hs)
  exact sq_pos_of_pos (mul_pos hsPos hsubPos)

end
end LFunctions
end Boundary
