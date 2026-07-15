import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSupportComparability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionDiscriminantNormalization

/-!
# Sharp support ratios for logarithmic dyadic blocks

The coarse factor six is sufficient for qualitative comparison but loses too
much in the fourth-power packet term.  Using `a ≥ 2` and `b + 1 ≤ 2a`
directly gives the sharp uniform ratios

`right / left ≤ 11/4` and `length / left ≤ 7/4`.

These are the endpoint constants used in the final tail arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Nat.le_sub_one_of_add_one_le
    {x y : ℕ} (h : x + 1 ≤ y) :
    x ≤ y - 1 := by
  exact Nat.le_sub_of_add_le h

theorem Nat.b_le_two_mul_a_sub_one
    {a b : ℕ} (hcomparable : b + 1 ≤ 2 * a) :
    b ≤ 2 * a - 1 := by
  exact Nat.le_sub_one_of_add_one_le hcomparable

theorem Real.b_cast_le_two_a_sub_one
    {a b : ℕ} (hcomparable : b + 1 ≤ 2 * a) :
    (b : ℝ) ≤ 2 * (a : ℝ) - 1 := by
  have hnat := Nat.b_le_two_mul_a_sub_one hcomparable
  have hcast : (b : ℝ) ≤ ((2 * a - 1 : ℕ) : ℝ) := Nat.cast_le.mpr hnat
  have honeLeB : 1 ≤ b + 1 := Nat.succ_le_succ (Nat.zero_le b)
  have honeLe : 1 ≤ 2 * a := le_trans honeLeB hcomparable
  have hcastSubRaw :
      ((2 * a - 1 : ℕ) : ℝ) =
        ((2 * a : ℕ) : ℝ) - ((1 : ℕ) : ℝ) :=
    Nat.cast_sub honeLe
  have hcastSub : ((2 * a - 1 : ℕ) : ℝ) = ((2 * a : ℕ) : ℝ) - 1 :=
    Eq.trans hcastSubRaw
      (congrArg (fun value : ℝ => ((2 * a : ℕ) : ℝ) - value)
        Nat.cast_one)
  have hcastMul : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) := Nat.cast_mul 2 a
  exact le_trans hcast
    (le_of_eq (Eq.trans hcastSub
      (congrArg (fun value : ℝ => value - 1) hcastMul)))

theorem Real.eleven_le_eighteen_for_logarithmicPhaseSupport :
    (11 : ℝ) ≤ 18 := by
  have hnat : (11 : ℕ) ≤ 18 :=
    le_trans (Nat.le_succ 11)
      (le_trans (Nat.le_succ 12)
        (le_trans (Nat.le_succ 13)
          (le_trans (Nat.le_succ 14)
            (le_trans (Nat.le_succ 15)
              (le_trans (Nat.le_succ 16) (Nat.le_succ 17))))))
  have hcast : ((11 : ℕ) : ℝ) ≤ ((18 : ℕ) : ℝ) :=
    Nat.cast_le.mpr hnat
  have helevenCast : ((11 : ℕ) : ℝ) = (11 : ℝ) := Nat.cast_ofNat
  have heighteenCast : ((18 : ℕ) : ℝ) = (18 : ℝ) := Nat.cast_ofNat
  have hleft : (11 : ℝ) ≤ ((18 : ℕ) : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ ((18 : ℕ) : ℝ))
      helevenCast hcast
  exact Eq.subst
    (motive := fun value : ℝ => (11 : ℝ) ≤ value)
    heighteenCast hleft

theorem Real.eight_mul_a_le_eleven_mul_a_sub_eleven_thirds
    {a : ℕ} (ha : 2 ≤ a) :
    8 * (a : ℝ) ≤ 11 * (a : ℝ) - 11 / 3 := by
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have hthreeA : (6 : ℝ) ≤ 3 * (a : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left haReal (Nat.cast_nonneg 3)
    have hthreeMulTwo : (3 : ℝ) * 2 = 6 :=
      Real.transition_nat_cast_mul 3 2 6 rfl
    exact le_trans (le_of_eq hthreeMulTwo.symm) hmul
  have helevenThirdLeSix : (11 : ℝ) / 3 ≤ 6 := by
    have hthreePos : (0 : ℝ) < 3 := zero_lt_three
    have hsixMulThree : (6 : ℝ) * 3 = 18 :=
      Real.transition_nat_cast_mul 6 3 18 rfl
    exact (div_le_iff₀ hthreePos).mpr
      (le_trans Real.eleven_le_eighteen_for_logarithmicPhaseSupport
        (le_of_eq hsixMulThree.symm))
  have hgap : (11 : ℝ) / 3 ≤ 3 * (a : ℝ) :=
    le_trans helevenThirdLeSix hthreeA
  have hadd :
      8 * (a : ℝ) + 11 / 3 ≤
        8 * (a : ℝ) + 3 * (a : ℝ) :=
    add_le_add_left hgap (8 * (a : ℝ))
  have heightAddThree : (8 : ℝ) + 3 = 11 :=
    Real.transition_nat_cast_add 8 3 11 rfl
  have hright :
      8 * (a : ℝ) + 3 * (a : ℝ) = 11 * (a : ℝ) :=
    Eq.trans (add_mul 8 3 (a : ℝ)).symm
      (congrArg (fun value : ℝ => value * (a : ℝ)) heightAddThree)
  have hsum :
      8 * (a : ℝ) + 11 / 3 ≤ 11 * (a : ℝ) :=
    le_trans hadd (le_of_eq hright)
  exact (le_sub_iff_add_le).mpr hsum

theorem Complex.natCast_le_seven_fourths_quantitativeSupportLeft
    {a : ℕ} (ha : 2 ≤ a) :
    (a : ℝ) ≤
      (7 / 4 : ℝ) *
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have hthreeA : (6 : ℝ) ≤ 3 * (a : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left haReal (Nat.cast_nonneg 3)
    have hthreeMulTwo : (3 : ℝ) * 2 = 6 :=
      Real.transition_nat_cast_mul 3 2 6 rfl
    exact le_trans (le_of_eq hthreeMulTwo.symm) hmul
  have hsevenLeElevenNat : (7 : ℕ) ≤ 11 :=
    le_trans (Nat.le_succ 7)
      (le_trans (Nat.le_succ 8)
        (le_trans (Nat.le_succ 9) (Nat.le_succ 10)))
  have hsevenLeEleven : (7 : ℝ) ≤ 11 := by
    have hcast : ((7 : ℕ) : ℝ) ≤ ((11 : ℕ) : ℝ) :=
      Nat.cast_le.mpr hsevenLeElevenNat
    have hsevenCast : ((7 : ℕ) : ℝ) = (7 : ℝ) := Nat.cast_ofNat
    have helevenCast : ((11 : ℕ) : ℝ) = (11 : ℝ) := Nat.cast_ofNat
    have hleft : (7 : ℝ) ≤ ((11 : ℕ) : ℝ) :=
      Eq.subst
        (motive := fun value : ℝ => value ≤ ((11 : ℕ) : ℝ))
        hsevenCast hcast
    exact Eq.subst
      (motive := fun value : ℝ => (7 : ℝ) ≤ value)
      helevenCast hleft
  have hsevenLeEighteen : (7 : ℝ) ≤ 18 :=
    le_trans hsevenLeEleven
      Real.eleven_le_eighteen_for_logarithmicPhaseSupport
  have hsevenThirdLeSix : (7 / 3 : ℝ) ≤ 6 := by
    have hsixMulThree : (6 : ℝ) * 3 = 18 :=
      Real.transition_nat_cast_mul 6 3 18 rfl
    exact (div_le_iff₀ zero_lt_three).mpr
      (le_trans hsevenLeEighteen (le_of_eq hsixMulThree.symm))
  have hsevenThirdLeThreeA : (7 / 3 : ℝ) ≤ 3 * (a : ℝ) :=
    le_trans hsevenThirdLeSix hthreeA
  have hadd :
      4 * (a : ℝ) + 7 / 3 ≤
        4 * (a : ℝ) + 3 * (a : ℝ) :=
    add_le_add_left hsevenThirdLeThreeA (4 * (a : ℝ))
  have hfourAddThree : (4 : ℝ) + 3 = 7 :=
    Real.transition_nat_cast_add 4 3 7 rfl
  have hright :
      4 * (a : ℝ) + 3 * (a : ℝ) = 7 * (a : ℝ) :=
    Eq.trans (add_mul 4 3 (a : ℝ)).symm
      (congrArg (fun value : ℝ => value * (a : ℝ)) hfourAddThree)
  have hcore :
      4 * (a : ℝ) ≤ 7 * (a : ℝ) - 7 / 3 :=
    (le_sub_iff_add_le).mpr (le_trans hadd (le_of_eq hright))
  have hcancel : (4 : ℝ) * (7 / 4) = 7 :=
    Eq.trans (mul_comm 4 (7 / 4))
      (div_mul_cancel₀ 7 (ne_of_gt zero_lt_four))
  have honeThird : (7 : ℝ) * (1 / 3) = 7 / 3 :=
    Eq.trans (mul_div_assoc 7 1 3).symm
      (congrArg (fun value : ℝ => value / 3) (mul_one 7))
  have hrightScaled :
      4 * ((7 / 4 : ℝ) * ((a : ℝ) - 1 / 3)) =
        7 * (a : ℝ) - 7 / 3 := by
    exact Eq.trans (mul_assoc 4 (7 / 4) _).symm
      (Eq.trans
        (congrArg (fun coefficient : ℝ => coefficient *
          ((a : ℝ) - 1 / 3)) hcancel)
        (Eq.trans (mul_sub 7 (a : ℝ) (1 / 3))
          (congrArg (fun value : ℝ => 7 * (a : ℝ) - value)
            honeThird)))
  have hscaled :
      4 * (a : ℝ) ≤
        4 * ((7 / 4 : ℝ) * ((a : ℝ) - 1 / 3)) :=
    le_trans hcore (le_of_eq hrightScaled.symm)
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  exact (mul_le_mul_left zero_lt_four).mp hscaled

theorem Complex.longGeometry_canonicalLength_le_seven_fourths_left
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    (((b + 1 : ℕ) : ℝ) - (a : ℝ)) ≤
      (7 / 4 : ℝ) *
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  have hcomparable :=
    Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry
  have hcast : ((b + 1 : ℕ) : ℝ) ≤ ((2 * a : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcomparable
  have htwoA : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) :=
    Nat.cast_mul 2 a
  have hright : ((b + 1 : ℕ) : ℝ) ≤ 2 * (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => ((b + 1 : ℕ) : ℝ) ≤ value)
      htwoA hcast
  have hsub := sub_le_sub_right hright (a : ℝ)
  have hnormalize : 2 * (a : ℝ) - (a : ℝ) = (a : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value - (a : ℝ))
        (two_mul (a : ℝ)))
      (add_sub_cancel_right (a : ℝ) (a : ℝ))
  have hlengthLeA :
      ((b + 1 : ℕ) : ℝ) - (a : ℝ) ≤ (a : ℝ) :=
    le_trans hsub (le_of_eq hnormalize)
  exact le_trans hlengthLeA
    (Complex.natCast_le_seven_fourths_quantitativeSupportLeft
      (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry))

theorem Complex.quantitativeSupportRight_le_eleven_fourths_left
    (a b : ℕ)
    (ha : 2 ≤ a)
    (hcomparable : b + 1 ≤ 2 * a) :
    Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤
      (11 / 4 : ℝ) *
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have hright :=
    Complex.quantitativeSupportRight_le_two_a a b hcomparable
  have hbase :
      2 * (a : ℝ) ≤
        (11 / 4 : ℝ) * ((a : ℝ) - 1 / 3) := by
    have hfourPos : (0 : ℝ) < 4 := zero_lt_four
    have hscaled :=
      Real.eight_mul_a_le_eleven_mul_a_sub_eleven_thirds ha
    have hleft : 4 * (2 * (a : ℝ)) = 8 * (a : ℝ) := by
      exact Eq.trans (mul_assoc 4 2 (a : ℝ)).symm
        (congrArg (fun value : ℝ => value * (a : ℝ))
          (Real.transition_nat_cast_mul 4 2 8 rfl))
    have hrightScaled :
        4 * ((11 / 4 : ℝ) * ((a : ℝ) - 1 / 3)) =
          11 * (a : ℝ) - 11 / 3 := by
      have hcancel : (4 : ℝ) * (11 / 4) = 11 := by
        exact Eq.trans (mul_comm 4 (11 / 4))
          (div_mul_cancel₀ 11 (ne_of_gt hfourPos))
      have honeThird : (11 : ℝ) * (1 / 3) = 11 / 3 := by
        exact Eq.trans (mul_div_assoc 11 1 3).symm
          (congrArg (fun value : ℝ => value / 3) (mul_one 11))
      exact Eq.trans (mul_assoc 4 (11 / 4) _).symm
        (Eq.trans
          (congrArg (fun coefficient : ℝ => coefficient *
            ((a : ℝ) - 1 / 3)) hcancel)
          (Eq.trans (mul_sub 11 (a : ℝ) (1 / 3))
            (congrArg (fun value : ℝ => 11 * (a : ℝ) - value)
              honeThird)))
    have hscaledTransport :
        4 * (2 * (a : ℝ)) ≤
          4 * ((11 / 4 : ℝ) * ((a : ℝ) - 1 / 3)) :=
      le_trans (le_of_eq hleft)
        (le_trans hscaled (le_of_eq hrightScaled.symm))
    exact (mul_le_mul_left hfourPos).mp hscaledTransport
  exact le_trans hright hbase

theorem Complex.quantitativeSupportLength_le_seven_fourths_left
    (a b : ℕ)
    (ha : 2 ≤ a)
    (hcomparable : b + 1 ≤ 2 * a) :
    Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) ≤
      (7 / 4 : ℝ) *
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLength
  have hright :=
    Complex.quantitativeSupportRight_le_eleven_fourths_left
      a b ha hcomparable
  have hsubtract := sub_le_sub_right hright
    (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))
  have hnormalize :
      (11 / 4 : ℝ) *
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) -
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) =
      (7 / 4 : ℝ) *
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
    let left := Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)
    have hone : (1 : ℝ) = 4 / 4 :=
      (div_self (ne_of_gt zero_lt_four)).symm
    have hsevenAddFour : (7 : ℝ) + 4 = 11 :=
      Real.transition_nat_cast_add 7 4 11 rfl
    have helevenSubFour : (11 : ℝ) - 4 = 7 :=
      (sub_eq_iff_eq_add).mpr hsevenAddFour.symm
    have hcoefficient : (11 / 4 : ℝ) - 1 = 7 / 4 := by
      calc
        (11 / 4 : ℝ) - 1 = 11 / 4 - 4 / 4 :=
          congrArg (fun value : ℝ => 11 / 4 - value) hone
        _ = (11 - 4) / 4 := (sub_div 11 4 4).symm
        _ = 7 / 4 :=
          congrArg (fun value : ℝ => value / 4) helevenSubFour
    calc
      (11 / 4 : ℝ) * left - left =
          (11 / 4 : ℝ) * left - 1 * left :=
        congrArg (fun value : ℝ => (11 / 4 : ℝ) * left - value)
          (one_mul left).symm
      _ = ((11 / 4 : ℝ) - 1) * left :=
        (sub_mul (11 / 4 : ℝ) 1 left).symm
      _ = (7 / 4 : ℝ) * left :=
        congrArg (fun value : ℝ => value * left) hcoefficient
  exact le_trans hsubtract (le_of_eq hnormalize)

theorem Complex.longGeometry_sharp_support_ratios
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤
        (11 / 4 : ℝ) *
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ∧
      Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) ≤
        (7 / 4 : ℝ) *
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  have ha := Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  have hcomparable :=
    Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry
  exact And.intro
    (Complex.quantitativeSupportRight_le_eleven_fourths_left
      a b ha hcomparable)
    (Complex.quantitativeSupportLength_le_seven_fourths_left
      a b ha hcomparable)

end
end LFunctions
end Boundary
