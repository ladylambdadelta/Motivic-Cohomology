import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteLeftInactiveCardinality
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarLowFrequency
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNumericalClosure

/-!
# Sharpened finite-inactive numerical closure

The full left-inactive family has cardinality one.  The right-far crossing
family is bounded by its side-specific frequency threshold.  These facts
replace the broad mode-range bounds used in the first numerical closure.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem sharpened_one_add_three_eq_four :
    (1 : ℝ) + 3 = 4 := by
  have hcast := realOfNat_add_eq_of_nat_eq 1 3 4 rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right)
      (Nat.cast_one (R := ℝ)).symm
      (Nat.cast_eq_ofNat (n := 3)).symm)
    (Eq.trans hcast (Nat.cast_eq_ofNat (n := 4)))

theorem Real.angular_endpoint_division_reassociate
    (norm endpoint angular : ℝ) :
    norm / (angular * endpoint) =
      (1 / angular) * (norm / endpoint) := by
  exact Eq.trans
    (congrArg (fun denominator : ℝ => norm / denominator)
      (mul_comm angular endpoint))
    (Eq.trans (div_div norm endpoint angular).symm
      (Eq.trans
        (div_eq_mul_inv (norm / endpoint) angular)
        (Eq.trans
          (mul_comm (norm / endpoint) angular⁻¹)
          (congrArg
            (fun factor : ℝ => factor * (norm / endpoint))
            (one_div angular).symm))))

theorem Real.right_threshold_le_one_third_scale
    (t : ℝ) (b : ℕ)
    (hbPos : 0 < (b : ℝ))
    (hsupport :
      ‖t‖ /
          (2 * Real.pi *
            Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)) ≤
        ‖t‖ / (2 * Real.pi * (b : ℝ)))
    (hbase : ‖t‖ / (b : ℝ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t) :
    ‖t‖ /
        (2 * Real.pi *
          Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)) ≤
      (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hangular :
      ‖t‖ / (2 * Real.pi * (b : ℝ)) ≤
        (1 / 6 : ℝ) * (‖t‖ / (b : ℝ)) := by
    have hinv := Real.reciprocal_two_pi_le_one_sixth
    have hmul := mul_le_mul_of_nonneg_right hinv
      (div_nonneg (norm_nonneg t) hbPos.le)
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      (Real.angular_endpoint_division_reassociate
        ‖t‖ (b : ℝ) (2 * Real.pi)).symm hmul
  have hscale := mul_le_mul_of_nonneg_left hbase
    (div_nonneg zero_le_one (Nat.cast_nonneg 6))
  have hnormalize :
      (1 / 6 : ℝ) *
          (2 * Complex.logarithmicPhaseBProcessScale t) =
        (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    have hsixNonzero : (6 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have htwoMulOne : (2 : ℝ) * 1 = 2 :=
      mul_one (2 : ℝ)
    have htwoMulThree : (2 : ℝ) * 3 = 6 :=
      realOfNat_mul_eq_of_nat_eq 2 3 6 rfl
    have honeMulSix : (1 : ℝ) * 6 = 6 :=
      one_mul (6 : ℝ)
    have htwoSixths : (2 / 6 : ℝ) = 1 / 3 :=
      (div_eq_div_iff hsixNonzero hthreeNonzero).mpr
        (htwoMulThree.trans honeMulSix.symm)
    have hcoefficient : (1 / 6 : ℝ) * 2 = 1 / 3 :=
      Eq.trans (mul_comm (1 / 6 : ℝ) 2)
        (Eq.trans (mul_div_assoc' 2 1 6)
          (Eq.trans
            (congrArg (fun numerator : ℝ => numerator / 6) htwoMulOne)
            htwoSixths))
    exact Eq.trans (mul_assoc (1 / 6 : ℝ) 2 _).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseBProcessScale t)
        hcoefficient)
  exact le_trans hsupport
    (le_trans hangular (le_trans hscale (le_of_eq hnormalize)))

theorem Real.right_crossing_coefficient_normalization
    (scale : ℝ) :
    (2 / 3 : ℝ) * ((1 / 3 : ℝ) * scale + scale) =
      (8 / 9 : ℝ) * scale := by
  have hthreeNonzero : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have honeMulThree : (1 : ℝ) * 3 = 3 :=
    one_mul (3 : ℝ)
  have honeAddThree : (1 : ℝ) + 3 = 4 :=
    sharpened_one_add_three_eq_four
  have hinsideCoefficient : (1 / 3 : ℝ) + 1 = 4 / 3 :=
    Eq.trans (div_add' 1 1 3 hthreeNonzero)
      (Eq.trans
        (congrArg (fun product : ℝ => (1 + product) / 3) honeMulThree)
        (congrArg (fun numerator : ℝ => numerator / 3) honeAddThree))
  have htwoMulFour : (2 : ℝ) * 4 = 8 :=
    realOfNat_mul_eq_of_nat_eq 2 4 8 rfl
  have hthreeMulThree : (3 : ℝ) * 3 = 9 :=
    realOfNat_mul_eq_of_nat_eq 3 3 9 rfl
  have hproduct : (2 / 3 : ℝ) * (4 / 3) = 8 / 9 :=
    Eq.trans (div_mul_div_comm 2 3 4 3)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        htwoMulFour hthreeMulThree)
  exact Eq.trans
    (congrArg (fun value : ℝ => (2 / 3 : ℝ) * value)
      (Eq.trans
        (congrArg (fun value : ℝ => (1 / 3 : ℝ) * scale + value)
          (one_mul scale).symm)
        (add_mul (1 / 3 : ℝ) 1 scale).symm))
    (Eq.trans (mul_assoc (2 / 3 : ℝ) (1 / 3 + 1) scale).symm
      (congrArg (fun coefficient : ℝ => coefficient * scale)
        (Eq.trans
          (congrArg (fun value : ℝ => (2 / 3 : ℝ) * value)
            hinsideCoefficient)
          hproduct)))

theorem Real.right_crossing_cardinality_coefficient_normalization
    (scale : ℝ) :
    ((1 / 3 : ℝ) * scale + scale) * (2 / 3 : ℝ) =
      (8 / 9 : ℝ) * scale :=
  Eq.trans
    (mul_comm
      ((1 / 3 : ℝ) * scale + scale) (2 / 3 : ℝ))
    (Real.right_crossing_coefficient_normalization scale)

theorem Complex.logarithmicPhaseFiniteLeftFarHighFrequency_budget_le_two_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hhigh : Complex.logarithmicPhaseFiniteLeftFarHighFrequency t a) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hcard := Complex.logarithmicPhaseFiniteLeftFar_card_le_one
    t ht (a : ℤ) (b : ℤ) hab
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have hmajorantNonneg :
      0 ≤ (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
      hscaleNonneg
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Finset.sum_le_one_mul_of_card_le_one
    (Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ))
    (fun m =>
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ))
    ((2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t)
    hcard hmajorantNonneg
    (fun m hm => by
      have hper :=
        Complex.logarithmicPhaseFiniteLeftFarHighFrequency_endpointScale_le_two_thirds_scale
          ht hhigh
      exact le_trans
        (Complex.logarithmicPhaseFiniteLeftFar_two_reciprocalGaps_le_perModeMajorant
          ht
          (Int.ofNat_le.mpr
            (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)) hm)
        hper)

theorem Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_two_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have haTwo :=
    Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  match Complex.logarithmicPhaseFiniteLeftFar_frequency_regime t a with
  | Or.inl hlow =>
      exact
        Complex.logarithmicPhaseFiniteLeftFarLowFrequency_budget_le_two_thirds_scale
          haTwo hlow
  | Or.inr hhigh =>
      exact
        Complex.logarithmicPhaseFiniteLeftFarHighFrequency_budget_le_two_thirds_scale
          ht hgeometry hhigh

theorem Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_three_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      3 * Complex.logarithmicPhaseBProcessScale t := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget_le_two_thirds_scale
      t ht a b hgeometry
  have hright :=
    Complex.logarithmicPhaseFiniteRightFarReciprocalBudget_le_seven_thirds_scale
      t ht a b hgeometry
  unfold Complex.logarithmicPhaseFiniteFarReciprocalBudget
  have hsum := add_le_add hleft hright
  have hcoefficient : (2 / 3 : ℝ) + 7 / 3 = 3 := by
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have htwoAddSeven : (2 : ℝ) + 7 = 9 :=
      realOfNat_add_eq_of_nat_eq 2 7 9 rfl
    have hnineThirds : (9 / 3 : ℝ) = 3 :=
      (div_eq_iff hthreeNonzero).mpr
        (realOfNat_mul_eq_of_nat_eq 3 3 9 rfl).symm
    exact Eq.trans (div_add_div_same 2 7 3)
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 3) htwoAddSeven)
        hnineThirds)
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (add_mul (2 / 3 : ℝ) (7 / 3)
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          hcoefficient)))

theorem Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_three_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      3 * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget
  exact Complex.logarithmicPhaseFiniteFarReciprocalBudget_le_three_scale
    t ht a b hgeometry

theorem Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_le_two_thirds_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hcard := Complex.logarithmicPhaseFiniteLeftFar_card_le_one
    t ht (a : ℤ) (b : ℤ) hab
  have hconstant := Finset.sum_le_one_mul_of_card_le_one
    (Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ))
    (fun _m : ℤ => (2 / 3 : ℝ)) (2 / 3 : ℝ)
    hcard (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
    (fun m hm => le_rfl)
  have hscale :=
    Complex.logarithmicPhaseFiniteNear_crossing_le_two_thirds_scale t
  unfold Complex.logarithmicPhaseFiniteLeftFarCrossingBudget
  exact le_trans hconstant hscale

theorem Complex.logarithmicPhaseFiniteRightFarCrossingBudget_le_eight_ninths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (8 / 9 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have ha := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hcard :=
    Complex.logarithmicPhaseFiniteRightFar_card_real_le_threshold_add_one
      t ht (a : ℤ) (b : ℤ) ha hab
  have hscaled := mul_le_mul_of_nonneg_right hcard
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  have hthreshold :
      Complex.logarithmicPhaseFiniteRightFrequencyThreshold t (b : ℤ) ≤
        (1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    unfold Complex.logarithmicPhaseFiniteRightFrequencyThreshold
    have hsupport : (b : ℝ) ≤
        Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ) :=
      Real.blockRight_le_quantitativeSupportRight b
    have hbPos := Real.logarithmicPhaseLongBranchGeometry_b_pos_real hgeometry
    have hdenom := mul_le_mul_of_nonneg_left hsupport
      Complex.two_mul_pi_pos.le
    have hquotient := div_le_div_of_nonneg_left (norm_nonneg t)
      (mul_pos Complex.two_mul_pi_pos hbPos) hdenom
    have hbase := Real.longGeometry_norm_div_b_le_two_scale ht hgeometry
    exact Real.right_threshold_le_one_third_scale
      t b (Real.logarithmicPhaseLongBranchGeometry_b_pos_real hgeometry)
      hquotient hbase
  have hone := Complex.logarithmicPhaseBProcessScale_one_le t
  have hinside := add_le_add hthreshold hone
  have houter := mul_le_mul_of_nonneg_right hinside
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  have hnormalize :
      ((1 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t +
          Complex.logarithmicPhaseBProcessScale t) * (2 / 3 : ℝ) =
        (8 / 9 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
    exact Real.right_crossing_cardinality_coefficient_normalization
      (Complex.logarithmicPhaseBProcessScale t)
  unfold Complex.logarithmicPhaseFiniteRightFarCrossingBudget
  have hconstant :=
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget_eq_card_mul
      t (a : ℤ) (b : ℤ)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hconstant.symm
    (le_trans hscaled (le_trans houter (le_of_eq hnormalize)))

theorem Complex.logarithmicPhaseFiniteFarCrossingBudget_le_fourteen_ninths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteFarCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (14 / 9 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hleft :=
    Complex.logarithmicPhaseFiniteLeftFarCrossingBudget_le_two_thirds_scale
      t ht a b hgeometry
  have hright :=
    Complex.logarithmicPhaseFiniteRightFarCrossingBudget_le_eight_ninths_scale
      t ht a b hgeometry
  unfold Complex.logarithmicPhaseFiniteFarCrossingBudget
  have hsum := add_le_add hleft hright
  have hcoefficient : (2 / 3 : ℝ) + 8 / 9 = 14 / 9 := by
    have hthreeNonzero : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    have hnineNonzero : (9 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 8))
    have htwoMulNine : (2 : ℝ) * 9 = 18 :=
      realOfNat_mul_eq_of_nat_eq 2 9 18 rfl
    have hsixMulThree : (6 : ℝ) * 3 = 18 :=
      realOfNat_mul_eq_of_nat_eq 6 3 18 rfl
    have htwoThirds : (2 / 3 : ℝ) = 6 / 9 :=
      (div_eq_div_iff hthreeNonzero hnineNonzero).mpr
        (htwoMulNine.trans hsixMulThree.symm)
    have hsixAddEight : (6 : ℝ) + 8 = 14 :=
      realOfNat_add_eq_of_nat_eq 6 8 14 rfl
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 8 / 9) htwoThirds)
      (Eq.trans (div_add_div_same 6 8 9)
        (congrArg (fun numerator : ℝ => numerator / 9) hsixAddEight))
  exact le_trans hsum
    (le_of_eq
      (Eq.trans
        (add_mul (2 / 3 : ℝ) (8 / 9)
          (Complex.logarithmicPhaseBProcessScale t)).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Complex.logarithmicPhaseBProcessScale t)
          hcoefficient)))

theorem Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget_le_fourteen_ninths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
        t (a : ℤ) (b : ℤ) ≤
      (14 / 9 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  unfold Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget
  exact Complex.logarithmicPhaseFiniteFarCrossingBudget_le_fourteen_ninths_scale
    t ht a b hgeometry

theorem Real.sharpened_finite_coefficients_eq_one_hundred_forty_five_eighteenths
    (scale : ℝ) :
    (7 / 2 : ℝ) * scale +
        (14 / 9 : ℝ) * scale + 3 * scale =
      (145 / 18 : ℝ) * scale := by
  have htwoNonzero : (2 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 1))
  have hnineNonzero : (9 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 8))
  have heighteenNonzero : (18 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 17))
  have hsevenMulEighteen : (7 : ℝ) * 18 = 126 :=
    realOfNat_mul_eq_of_nat_eq 7 18 126 rfl
  have hsixtyThreeMulTwo : (63 : ℝ) * 2 = 126 :=
    realOfNat_mul_eq_of_nat_eq 63 2 126 rfl
  have hsevenHalves : (7 / 2 : ℝ) = 63 / 18 :=
    (div_eq_div_iff htwoNonzero heighteenNonzero).mpr
      (hsevenMulEighteen.trans hsixtyThreeMulTwo.symm)
  have hfourteenMulEighteen : (14 : ℝ) * 18 = 252 :=
    realOfNat_mul_eq_of_nat_eq 14 18 252 rfl
  have htwentyEightMulNine : (28 : ℝ) * 9 = 252 :=
    realOfNat_mul_eq_of_nat_eq 28 9 252 rfl
  have hfourteenNinths : (14 / 9 : ℝ) = 28 / 18 :=
    (div_eq_div_iff hnineNonzero heighteenNonzero).mpr
      (hfourteenMulEighteen.trans htwentyEightMulNine.symm)
  have hfiftyFourDivEighteen : (54 / 18 : ℝ) = 3 :=
    (div_eq_iff heighteenNonzero).mpr
      (realOfNat_mul_eq_of_nat_eq 3 18 54 rfl).symm
  have hthree : (3 : ℝ) = 54 / 18 := hfiftyFourDivEighteen.symm
  have hsixtyThreeAddTwentyEight : (63 : ℝ) + 28 = 91 :=
    realOfNat_add_eq_of_nat_eq 63 28 91 rfl
  have hninetyOneAddFiftyFour : (91 : ℝ) + 54 = 145 :=
    realOfNat_add_eq_of_nat_eq 91 54 145 rfl
  have hcoefficient :
      (7 / 2 : ℝ) + 14 / 9 + 3 = 145 / 18 :=
    Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          hsevenHalves hfourteenNinths)
        hthree)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 54 / 18)
          (div_add_div_same 63 28 18))
        (Eq.trans
          (congrArg
            (fun numerator : ℝ => numerator / 18 + 54 / 18)
            hsixtyThreeAddTwentyEight)
          (Eq.trans (div_add_div_same 91 54 18)
            (congrArg (fun numerator : ℝ => numerator / 18)
              hninetyOneAddFiftyFour))))
  exact Eq.trans
    (Eq.trans
      (congrArg (fun value : ℝ => value + 3 * scale)
        (add_mul (7 / 2 : ℝ) (14 / 9) scale).symm)
      (add_mul ((7 / 2 : ℝ) + 14 / 9) 3 scale).symm)
    (congrArg (fun coefficient : ℝ => coefficient * scale)
      hcoefficient)

theorem Complex.logarithmicPhaseFiniteInactiveSharpBudget_le_one_hundred_forty_five_eighteenths_scale
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseFiniteInactiveSharpBudget
        t (a : ℤ) (b : ℤ) ≤
      (145 / 18 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hstationary :=
    Complex.logarithmicPhaseFiniteInactiveSharpStationaryBudget_le_seven_halves_scale
      ht ht_nonneg hgeometry
  have hcrossing :=
    Complex.logarithmicPhaseFiniteInactiveSharpCrossingBudget_le_fourteen_ninths_scale
      t ht a b hgeometry
  have hreciprocal :=
    Complex.logarithmicPhaseFiniteInactiveSharpReciprocalBudget_le_three_scale
      t ht a b hgeometry
  have hparts :=
    Complex.logarithmicPhaseFiniteInactiveSharpBudget_eq_three_parts
      t (a : ℤ) (b : ℤ)
  have hsum := add_le_add (add_le_add hstationary hcrossing) hreciprocal
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hparts.symm
    (le_trans hsum
      (le_of_eq
        (Real.sharpened_finite_coefficients_eq_one_hundred_forty_five_eighteenths
          (Complex.logarithmicPhaseBProcessScale t))))

end

end LFunctions
end Boundary
