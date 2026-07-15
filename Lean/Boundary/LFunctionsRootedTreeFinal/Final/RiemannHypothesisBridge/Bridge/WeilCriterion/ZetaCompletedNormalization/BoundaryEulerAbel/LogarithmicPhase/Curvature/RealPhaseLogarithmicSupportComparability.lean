import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedFarNegativeTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicLongGeometry

/-!
# Quantitative support comparability on long dyadic blocks

The phase-adapted tail coefficients are evaluated at the left cutoff endpoint,
whereas the positive frequency shift is evaluated at the right endpoint.  The
canonical dyadic inequality `b + 1 ≤ 2a` controls this mismatch.  This owner
derives explicit support comparisons, with constants chosen to remain valid at
the smallest possible long block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.one_le_three_for_logarithmicPhaseSupport :
    (1 : ℝ) ≤ 3 := by
  have hraw :
      ((Nat.succ 0 : ℕ) : ℝ) ≤ ((Nat.succ 2 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le 2))
  have honeCast : ((Nat.succ 0 : ℕ) : ℝ) = (1 : ℝ) :=
    Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ))
        (show (Nat.succ 0 : ℕ) = 1 from rfl))
      Nat.cast_one
  have hthreeCast : ((Nat.succ 2 : ℕ) : ℝ) = (3 : ℝ) :=
    Eq.trans
      (congrArg (fun n : ℕ => (n : ℝ))
        (show (Nat.succ 2 : ℕ) = 3 from rfl))
      Nat.cast_ofNat
  have hleft : (1 : ℝ) ≤ ((Nat.succ 2 : ℕ) : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ ((Nat.succ 2 : ℕ) : ℝ))
      honeCast hraw
  exact Eq.subst
    (motive := fun value : ℝ => (1 : ℝ) ≤ value)
    hthreeCast hleft

theorem Real.three_add_three_eq_six_for_logarithmicPhaseSupport :
    (3 : ℝ) + 3 = 6 := by
  have hthreeCast : ((3 : ℕ) : ℝ) = (3 : ℝ) := Nat.cast_ofNat
  have hsixCast : ((6 : ℕ) : ℝ) = (6 : ℝ) := Nat.cast_ofNat
  calc
    (3 : ℝ) + 3 = ((3 : ℕ) : ℝ) + ((3 : ℕ) : ℝ) :=
      congrArg₂ (fun left right : ℝ => left + right)
        hthreeCast.symm hthreeCast.symm
    _ = (((3 + 3 : ℕ) : ℕ) : ℝ) := (Nat.cast_add 3 3).symm
    _ = ((6 : ℕ) : ℝ) :=
      congrArg (fun n : ℕ => (n : ℝ))
        (show (3 + 3 : ℕ) = 6 from rfl)
    _ = (6 : ℝ) := hsixCast

theorem Nat.two_le_of_strict_and_successor_le_two_mul
    {a b : ℕ}
    (hab : a < b)
    (hcomparable : b + 1 ≤ 2 * a) :
    2 ≤ a := by
  have hasucc : a + 1 ≤ b := Nat.succ_le_of_lt hab
  have hasuccsucc : a + 1 + 1 ≤ b + 1 :=
    Nat.add_le_add_right hasucc 1
  have haTwo : a + 2 ≤ b + 1 := by
    have hnormalize : a + 1 + 1 = a + 2 := by
      exact Eq.trans (Nat.add_assoc a 1 1)
        (congrArg (fun value : ℕ => a + value) (show 1 + 1 = 2 from rfl))
    exact le_trans (le_of_eq hnormalize.symm) hasuccsucc
  have hdouble : 2 * a = a + a := by
    exact Nat.two_mul a
  have hcomparableNormalized : b + 1 ≤ a + a :=
    le_trans hcomparable (le_of_eq hdouble)
  have hcancelable : a + 2 ≤ a + a :=
    le_trans haTwo hcomparableNormalized
  exact Nat.le_of_add_le_add_left hcancelable

theorem Real.logarithmicPhaseLongBranchGeometry_two_le_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    2 ≤ a := by
  exact Nat.two_le_of_strict_and_successor_le_two_mul
    (Real.logarithmicPhaseLongBranchGeometry_strict hgeometry)
    (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)

theorem Real.two_thirds_le_a_cast
    {a : ℕ} (ha : 2 ≤ a) :
    (2 : ℝ) / 3 ≤ (a : ℝ) := by
  have htwoCast : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have hthreePos : (0 : ℝ) < 3 := zero_lt_three
  have honeThird : (2 : ℝ) / 3 ≤ 2 := by
    have honeLeThree : (1 : ℝ) ≤ 3 :=
      Real.one_le_three_for_logarithmicPhaseSupport
    have hdivLeOne : (1 : ℝ) / 3 ≤ 1 :=
      (div_le_one hthreePos).mpr honeLeThree
    have hmul := mul_le_mul_of_nonneg_left hdivLeOne zero_le_two
    have hleft : (2 : ℝ) * (1 / 3) = 2 / 3 := by
      exact Eq.trans (congrArg (fun value : ℝ => 2 * value) (one_div 3))
        (div_eq_mul_inv 2 3).symm
    have hright : (2 : ℝ) * 1 = 2 := mul_one 2
    exact le_trans (le_of_eq hleft.symm)
      (le_trans hmul (le_of_eq hright))
  exact le_trans honeThird htwoCast

theorem Complex.quantitativeSupportLeft_pos_of_two_le
    (a : ℕ) (ha : 2 ≤ a) :
    0 < Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  have hone : (1 : ℤ) ≤ (a : ℤ) :=
    Int.ofNat_le.mpr (le_trans one_le_two ha)
  exact Complex.logarithmicPhaseQuantitativeSupportLeft_pos (a : ℤ) hone

theorem Complex.one_third_a_le_quantitativeSupportLeft
    (a : ℕ) (ha : 2 ≤ a) :
    (a : ℝ) / 3 ≤
      Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have haNonneg : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
  have honeReal : (1 : ℝ) ≤ (a : ℝ) :=
    le_trans one_le_two haReal
  have haPlusOneLeTwoA : (a : ℝ) + 1 ≤ (a : ℝ) + (a : ℝ) :=
    add_le_add_left honeReal (a : ℝ)
  have hTwoALeThreeA : (a : ℝ) + (a : ℝ) ≤ (a : ℝ) * 3 := by
    have htwoLeThree : (2 : ℝ) ≤ 3 :=
      Nat.cast_le.mpr (Nat.le_succ 2)
    have hmul : 2 * (a : ℝ) ≤ 3 * (a : ℝ) :=
      mul_le_mul_of_nonneg_right htwoLeThree haNonneg
    have hleft : (a : ℝ) + (a : ℝ) = 2 * (a : ℝ) :=
      (two_mul (a : ℝ)).symm
    have hright : 3 * (a : ℝ) = (a : ℝ) * 3 :=
      mul_comm 3 (a : ℝ)
    exact le_trans (le_of_eq hleft)
      (le_trans hmul (le_of_eq hright))
  have haPlusOneLeThreeA : (a : ℝ) + 1 ≤ (a : ℝ) * 3 :=
    le_trans haPlusOneLeTwoA hTwoALeThreeA
  have hthreePos : (0 : ℝ) < 3 := zero_lt_three
  have hfraction : ((a : ℝ) + 1) / 3 ≤ (a : ℝ) :=
    (div_le_iff₀ hthreePos).mpr haPlusOneLeThreeA
  have haddDiv : (a : ℝ) / 3 + 1 / 3 = ((a : ℝ) + 1) / 3 :=
    (add_div (a : ℝ) 1 3).symm
  have hsum : (a : ℝ) / 3 + 1 / 3 ≤ (a : ℝ) :=
    le_trans (le_of_eq haddDiv) hfraction
  exact (le_sub_iff_add_le).mpr hsum

theorem Complex.quantitativeSupportRight_le_two_a
    (a b : ℕ)
    (hcomparable : b + 1 ≤ 2 * a) :
    Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤
      2 * (a : ℝ) := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have honeThirdLeOne : (1 : ℝ) / 3 ≤ 1 := by
    have hthreePos : (0 : ℝ) < 3 := zero_lt_three
    have honeLeThree : (1 : ℝ) ≤ 3 :=
      Real.one_le_three_for_logarithmicPhaseSupport
    exact (div_le_one hthreePos).mpr honeLeThree
  have hfirst := add_le_add_left honeThirdLeOne (b : ℝ)
  have hsuccCast : (b : ℝ) + 1 = ((b + 1 : ℕ) : ℝ) :=
    Eq.trans
      (congrArg (fun value : ℝ => (b : ℝ) + value) Nat.cast_one.symm)
      (Nat.cast_add b 1).symm
  have hcomparableReal : ((b + 1 : ℕ) : ℝ) ≤ ((2 * a : ℕ) : ℝ) :=
    Nat.cast_le.mpr hcomparable
  have hmulCast : ((2 * a : ℕ) : ℝ) = 2 * (a : ℝ) :=
    Nat.cast_mul 2 a
  exact le_trans hfirst
    (le_trans (le_of_eq hsuccCast) (Eq.subst hmulCast hcomparableReal))

theorem Complex.quantitativeSupportRight_le_six_mul_left
    (a b : ℕ)
    (ha : 2 ≤ a)
    (hcomparable : b + 1 ≤ 2 * a) :
    Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤
      6 * Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  have hright :=
    Complex.quantitativeSupportRight_le_two_a a b hcomparable
  have hleft :=
    Complex.one_third_a_le_quantitativeSupportLeft a ha
  have hsix := mul_le_mul_of_nonneg_left hleft (Nat.cast_nonneg 6)
  have hnormalize : 6 * ((a : ℝ) / 3) = 2 * (a : ℝ) := by
    have hthreeNe : (3 : ℝ) ≠ 0 := ne_of_gt zero_lt_three
    have hsixEqTwoMulThree : (6 : ℝ) = 2 * 3 :=
      (Eq.trans (two_mul (3 : ℝ))
        Real.three_add_three_eq_six_for_logarithmicPhaseSupport).symm
    have hsixDivThree : (6 : ℝ) / 3 = 2 :=
      (div_eq_iff hthreeNe).mpr hsixEqTwoMulThree
    calc
      6 * ((a : ℝ) / 3) = (6 * (a : ℝ)) / 3 :=
        (mul_div_assoc 6 (a : ℝ) 3).symm
      _ = ((a : ℝ) * 6) / 3 :=
        congrArg (fun value : ℝ => value / 3) (mul_comm 6 (a : ℝ))
      _ = (a : ℝ) * (6 / 3) :=
        mul_div_assoc (a : ℝ) 6 3
      _ = (a : ℝ) * 2 :=
        congrArg (fun value : ℝ => (a : ℝ) * value) hsixDivThree
      _ = 2 * (a : ℝ) := mul_comm (a : ℝ) 2
  exact le_trans hright
    (le_trans (le_of_eq hnormalize.symm) hsix)

theorem Complex.longGeometry_quantitativeSupportRight_le_six_mul_left
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) ≤
      6 * Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) := by
  exact Complex.quantitativeSupportRight_le_six_mul_left a b
    (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
    (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)

end
end LFunctions
end Boundary
