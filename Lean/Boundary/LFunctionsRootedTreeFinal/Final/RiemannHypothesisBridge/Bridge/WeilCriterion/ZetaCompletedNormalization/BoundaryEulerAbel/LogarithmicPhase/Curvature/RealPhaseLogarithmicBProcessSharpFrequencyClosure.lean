import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessSharpActiveClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicPositiveTailArithmetic

/-!
# Six-fold sharpening of the active frequency-cardinality term

The earlier cardinal arithmetic used only a unit lower bound for `2*pi`.
Combining `2*pi > 6` with `a - 2/3 >= a/3` gives a denominator at least
`2*a`, hence a frequency term at most `norm t/(2*a)`.  This sharpens all four
frequency-weighted products simultaneously.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem real_three_mul_two_eq_six :
    (3 : ℝ) * 2 = 6 :=
  realOfNat_mul_eq_of_nat_eq 3 2 6 rfl

private theorem Real.half_mul_product_mul_two_mul
    (x y : ℝ) :
    ((1 / 2 : ℝ) * x) * (2 * y) = x * y := by
  have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
  have hhalfTwo : (1 / 2 : ℝ) * 2 = 1 :=
    div_mul_cancel₀ 1 htwoNe
  calc
    ((1 / 2 : ℝ) * x) * (2 * y) =
        ((1 / 2) * 2) * (x * y) :=
      mul_mul_mul_comm (1 / 2) x 2 y
    _ = 1 * (x * y) :=
      congrArg (fun value : ℝ => value * (x * y)) hhalfTwo
    _ = x * y := one_mul _

private theorem Real.six_mul_product_eq_of_three_two_product_eq
    (x y z : ℝ)
    (h : (3 * x) * (2 * y) = 6 * z) :
    x * y = z := by
  have hleft : (3 * x) * (2 * y) = 6 * (x * y) := by
    exact Eq.trans (mul_mul_mul_comm 3 x 2 y)
      (congrArg (fun value : ℝ => value * (x * y))
        real_three_mul_two_eq_six)
  have hsixEq : 6 * (x * y) = 6 * z := Eq.trans hleft.symm h
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  exact mul_left_cancel₀ hsixNe hsixEq

theorem Real.longGeometry_two_mul_a_le_angular_leftSupport
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    2 * (a : ℝ) ≤
      2 * Real.pi *
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hleft :
      (a : ℝ) / 3 ≤
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    Real.longGeometry_one_third_a_le_cutoffSupportLeft hgeometry
  have hsix : (6 : ℝ) ≤ 2 * Real.pi :=
    Real.two_mul_pi_ge_six.le
  have hsixNonneg : (0 : ℝ) ≤ 6 := Nat.cast_nonneg 6
  have hfirstProduct := mul_le_mul_of_nonneg_right hleft hsixNonneg
  have hleftNonneg : 0 ≤ (a : ℝ) / 3 :=
    div_nonneg haPos.le (Nat.cast_nonneg 3)
  have hendpointNonneg :
      0 ≤ Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    le_trans hleftNonneg hleft
  have hsecondProduct :=
    mul_le_mul_of_nonneg_left hsix hendpointNonneg
  have hscaleLeft := le_trans hfirstProduct hsecondProduct
  have hleftNormalize :
      ((a : ℝ) / 3) * 6 = 2 * (a : ℝ) := by
    have hthreeNe : (3 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
    calc
      ((a : ℝ) / 3) * 6 = (a : ℝ) * (6 / 3) := by
        exact Eq.trans
          (congrArg (fun value : ℝ => value * 6)
            (div_eq_mul_inv (a : ℝ) 3))
          (Eq.trans (mul_assoc (a : ℝ) 3⁻¹ 6)
            (congrArg (fun value : ℝ => (a : ℝ) * value)
              (Eq.trans (mul_comm 3⁻¹ 6)
                (div_eq_mul_inv 6 3).symm)))
      _ = (a : ℝ) * 2 := by
        have hproduct : (2 : ℝ) * 3 = 6 :=
          realOfNat_mul_eq_of_nat_eq 2 3 6 rfl
        exact congrArg (fun value : ℝ => (a : ℝ) * value)
          ((div_eq_iff hthreeNe).mpr hproduct.symm)
      _ = 2 * (a : ℝ) := mul_comm _ _
  have hrightNormalize :
      Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) *
          (2 * Real.pi) =
        2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) :=
    mul_comm _ _
  have hscaleRight := le_trans hscaleLeft (le_of_eq hrightNormalize)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ 2 * Real.pi *
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ))
    hleftNormalize hscaleRight

theorem Real.longGeometry_frequencyCardTerm_le_half_norm_div_a
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) ≤
      (1 / 2 : ℝ) * (‖t‖ / (a : ℝ)) := by
  have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
    (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hdenominator :=
    Real.longGeometry_two_mul_a_le_angular_leftSupport hgeometry
  have htwoPos : (0 : ℝ) < 2 := zero_lt_two
  have htwoA : 0 < 2 * (a : ℝ) := mul_pos htwoPos haPos
  have hdivision := div_le_div_of_nonneg_left
    (norm_nonneg t) htwoA hdenominator
  have hnormalize :
      ‖t‖ / (2 * (a : ℝ)) =
        (1 / 2 : ℝ) * (‖t‖ / (a : ℝ)) := by
    have hquotientProduct :=
      Real.div_mul_div_eq_mul_div_mul 1 2 ‖t‖ (a : ℝ)
    calc
      ‖t‖ / (2 * (a : ℝ)) = (1 * ‖t‖) / (2 * (a : ℝ)) := by
        exact congrArg (fun value : ℝ => value / (2 * (a : ℝ)))
          (one_mul ‖t‖).symm
      _ = (1 / 2 : ℝ) * (‖t‖ / (a : ℝ)) :=
        hquotientProduct.symm
  exact le_trans hdivision (le_of_eq hnormalize)

theorem Complex.sharpFrequencyScalar_mul_crossingScalar_le_two_thirds_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessCrossingScalar ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_half_norm_div_a hgeometry
  have hproduct := mul_le_mul_of_nonneg_right hfrequency
    Complex.logarithmicPhaseBProcessCrossingScalar_nonneg
  have hnormalize :
      ((1 / 2 : ℝ) * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessCrossingScalar =
        (2 / 3 : ℝ) * (‖t‖ / (a : ℝ)) := by
    unfold Complex.logarithmicPhaseBProcessCrossingScalar
    calc
      ((1 / 2) * (‖t‖ / (a : ℝ))) * (4 / 3) =
          ((1 / 2) * (4 / 3)) * (‖t‖ / (a : ℝ)) := by
        exact Eq.trans (mul_assoc _ _ _)
          (Eq.trans
            (congrArg (fun value : ℝ => (1 / 2) * value)
              (mul_comm _ _))
            (mul_assoc _ _ _).symm)
      _ = (2 / 3) * (‖t‖ / (a : ℝ)) := by
        exact congrArg (fun value : ℝ => value * (‖t‖ / (a : ℝ)))
          (show (1 / 2 : ℝ) * (4 / 3) = 2 / 3 from by
            have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
            have hhalfTwo : (1 / 2 : ℝ) * 2 = 1 :=
              div_mul_cancel₀ 1 htwoNe
            have htwoTwo : (2 : ℝ) * 2 = 4 :=
              realOfNat_mul_eq_of_nat_eq 2 2 4 rfl
            have hhalfFour : (1 / 2 : ℝ) * 4 = 2 := by
              exact Eq.trans
                (congrArg (fun value : ℝ => (1 / 2) * value) htwoTwo.symm)
                (Eq.trans (mul_assoc (1 / 2) 2 2).symm
                  (Eq.trans
                    (congrArg (fun value : ℝ => value * 2) hhalfTwo)
                    (one_mul 2)))
            exact Eq.trans (mul_div_assoc (1 / 2) 4 3).symm
              (congrArg (fun value : ℝ => value / 3) hhalfFour))
  have hscale := Real.longGeometry_norm_div_a_le_scale hgeometry
  have htwoThirdsNonneg : (0 : ℝ) ≤ 2 / 3 :=
    div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
  have hscaled := mul_le_mul_of_nonneg_left hscale
    htwoThirdsNonneg
  exact le_trans hproduct (le_trans (le_of_eq hnormalize) hscaled)

theorem Complex.sharpFrequencyScalar_mul_tailScalar_le_two_scale
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_half_norm_div_a hgeometry
  have htail := Complex.logarithmicPhaseBProcessTailScalar_nonneg
    t ht (Int.ofNat_zero_le b)
  have hproduct := mul_le_mul_of_nonneg_right hfrequency htail
  have hnormalize :
      ((1 / 2 : ℝ) * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ) =
        ((b : ℝ) / (a : ℝ)) *
          Complex.logarithmicPhaseBProcessScale t := by
    unfold Complex.logarithmicPhaseBProcessTailScalar
    have hnormNe := ne_of_gt
      (Complex.logarithmicPhaseBProcess_norm_pos t ht)
    have haPos : 0 < (a : ℝ) := Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
    have haNe : (a : ℝ) ≠ 0 := ne_of_gt haPos
    have hbase := Real.three_norm_div_a_mul_two_b_scale_div_norm_eq
      ‖t‖ (a : ℝ) (b : ℝ)
      (Complex.logarithmicPhaseBProcessScale t) hnormNe haNe
    have hcancel :=
      Real.six_mul_product_eq_of_three_two_product_eq
        (‖t‖ / (a : ℝ))
        ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖)
        (((b : ℝ) / (a : ℝ)) *
          Complex.logarithmicPhaseBProcessScale t)
        hbase
    exact Eq.trans
      (Real.half_mul_product_mul_two_mul
        (‖t‖ / (a : ℝ))
        ((b : ℝ) * Complex.logarithmicPhaseBProcessScale t / ‖t‖))
      hcancel
  have hratio := Real.longGeometry_b_div_a_le_two hgeometry
  have hscaled := mul_le_mul_of_nonneg_right hratio
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact le_trans hproduct (le_trans (le_of_eq hnormalize) hscaled)

theorem Complex.sharpFrequencyScalar_mul_centralScalar_le_two_scale
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ) *
        Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ) ≤
      2 * Complex.logarithmicPhaseBProcessScale t := by
  have hfrequency :=
    Real.longGeometry_frequencyCardTerm_le_half_norm_div_a hgeometry
  have hcentral := Complex.logarithmicPhaseBProcessCentralScalar_nonneg
    t (Int.ofNat_zero_le b)
  have hproduct := mul_le_mul_of_nonneg_right hfrequency hcentral
  have hratio := Real.longGeometry_b_div_a_le_two hgeometry
  have hnormScale :=
    Complex.logarithmicPhaseBProcess_norm_div_scale_le_scale t
  have hnormDivScaleNonneg :
      0 ≤ ‖t‖ / Complex.logarithmicPhaseBProcessScale t :=
    div_nonneg (norm_nonneg t)
      (Complex.logarithmicPhaseBProcessScale_nonneg t)
  have hratioProduct :=
    mul_le_mul_of_nonneg_right hratio hnormDivScaleNonneg
  have htwoNonneg : (0 : ℝ) ≤ 2 := Nat.cast_nonneg 2
  have hscaleProduct :=
    mul_le_mul_of_nonneg_left hnormScale htwoNonneg
  have hmul := le_trans hratioProduct hscaleProduct
  have hnormalize :
      ((1 / 2 : ℝ) * (‖t‖ / (a : ℝ))) *
          Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ) =
        ((b : ℝ) / (a : ℝ)) *
          (‖t‖ / Complex.logarithmicPhaseBProcessScale t) := by
    unfold Complex.logarithmicPhaseBProcessCentralScalar
    have hbase := Real.three_norm_div_a_mul_two_b_div_scale_eq
      ‖t‖ (a : ℝ) (b : ℝ)
      (Complex.logarithmicPhaseBProcessScale t)
    have hcancel :=
      Real.six_mul_product_eq_of_three_two_product_eq
        (‖t‖ / (a : ℝ))
        ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t)
        (((b : ℝ) / (a : ℝ)) *
          (‖t‖ / Complex.logarithmicPhaseBProcessScale t))
        hbase
    exact Eq.trans
      (Real.half_mul_product_mul_two_mul
        (‖t‖ / (a : ℝ))
        ((b : ℝ) / Complex.logarithmicPhaseBProcessScale t))
      hcancel
  exact le_trans hproduct (le_trans (le_of_eq hnormalize) hmul)

theorem Real.sharp_frequency_active_coefficient_sum_eq_one_hundred_one_thirds :
    ((3 : ℝ) + 8 + 8 + 8) +
      ((2 / 3 : ℝ) + 2 + 2 + 2) = 101 / 3 := by
  have hthreeNe : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hthreeEight : (3 : ℝ) + 8 = 11 :=
    realOfNat_add_eq_of_nat_eq 3 8 11 rfl
  have helevenEight : (11 : ℝ) + 8 = 19 :=
    realOfNat_add_eq_of_nat_eq 11 8 19 rfl
  have hnineteenEight : (19 : ℝ) + 8 = 27 :=
    realOfNat_add_eq_of_nat_eq 19 8 27 rfl
  have hleft : (3 : ℝ) + 8 + 8 + 8 = 27 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 8 + 8) hthreeEight)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 8) helevenEight)
        hnineteenEight)
  have htwoMulThree : (2 : ℝ) * 3 = 6 :=
    realOfNat_mul_eq_of_nat_eq 2 3 6 rfl
  have htwoEqSixThirds : (2 : ℝ) = 6 / 3 :=
    (eq_div_iff hthreeNe).mpr htwoMulThree
  have hreplaceTwos :
      (2 / 3 : ℝ) + 2 + 2 + 2 =
        2 / 3 + 6 / 3 + 6 / 3 + 6 / 3 :=
    congrArg (fun value : ℝ => 2 / 3 + value + value + value)
      htwoEqSixThirds
  have hfirst : (2 / 3 : ℝ) + 6 / 3 = (2 + 6) / 3 :=
    div_add_div_same 2 6 3
  have hsecond : ((2 + 6 : ℝ) / 3) + 6 / 3 =
      ((2 + 6) + 6) / 3 :=
    div_add_div_same (2 + 6) 6 3
  have hthird : (((2 + 6 : ℝ) + 6) / 3) + 6 / 3 =
      (((2 + 6) + 6) + 6) / 3 :=
    div_add_div_same ((2 + 6 : ℝ) + 6) 6 3
  have htwoSix : (2 : ℝ) + 6 = 8 :=
    realOfNat_add_eq_of_nat_eq 2 6 8 rfl
  have heightSix : (8 : ℝ) + 6 = 14 :=
    realOfNat_add_eq_of_nat_eq 8 6 14 rfl
  have hfourteenSix : (14 : ℝ) + 6 = 20 :=
    realOfNat_add_eq_of_nat_eq 14 6 20 rfl
  have hnumerator : ((2 + 6 : ℝ) + 6) + 6 = 20 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 6 + 6) htwoSix)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 6) heightSix)
        hfourteenSix)
  have hright : (2 / 3 : ℝ) + 2 + 2 + 2 = 20 / 3 :=
    Eq.trans hreplaceTwos
      (Eq.trans
        (congrArg (fun value : ℝ => value + 6 / 3 + 6 / 3) hfirst)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 6 / 3) hsecond)
          (Eq.trans hthird
            (congrArg (fun numerator : ℝ => numerator / 3) hnumerator))))
  have htwentySevenMulThree : (27 : ℝ) * 3 = 81 :=
    realOfNat_mul_eq_of_nat_eq 27 3 81 rfl
  have hleftThirds : (27 : ℝ) = 81 / 3 :=
    (eq_div_iff hthreeNe).mpr htwentySevenMulThree
  have hcombine : (81 / 3 : ℝ) + 20 / 3 = (81 + 20) / 3 :=
    div_add_div_same 81 20 3
  have hnumeratorFinal : (81 : ℝ) + 20 = 101 :=
    realOfNat_add_eq_of_nat_eq 81 20 101 rfl
  exact Eq.trans
    (congrArg₂ (fun left right : ℝ => left + right) hleft hright)
    (Eq.trans
      (congrArg (fun value : ℝ => value + 20 / 3) hleftThirds)
      (Eq.trans hcombine
        (congrArg (fun numerator : ℝ => numerator / 3)
          hnumeratorFinal)))

theorem Complex.logarithmicPhaseBProcessClosedInteriorMajorant_le_thirty_four_scale_of_nonempty
    {t : ℝ} {a b : ℕ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hnonempty :
      (Complex.logarithmicPhasePoissonBProcessInteriorModes
        t (a : ℤ) (b : ℤ)).Nonempty) :
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant
        t (a : ℤ) (b : ℤ) ≤
      34 * Complex.logarithmicPhaseBProcessScale t := by
  let S := Complex.logarithmicPhaseBProcessScale t
  let C := Complex.logarithmicPhaseBProcessCrossingScalar
  let L := Complex.logarithmicPhaseBProcessTailScalar t (b : ℤ)
  let M := Complex.logarithmicPhaseBProcessCentralScalar t (b : ℤ)
  let F := Complex.logarithmicPhaseBProcessFrequencyCardScalar t (a : ℤ)
  have hexpand :=
    Complex.logarithmicPhaseBProcessClosedInteriorMajorant_eq_eight_products
      t (a : ℤ) (b : ℤ)
  have hxC := Complex.two_mul_crossingScalar_le_three_mul_scale t
  have hxL := Complex.two_mul_tailScalar_le_eight_mul_scale_of_nonempty
    ht hgeometry hnonempty
  have hxM := Complex.two_mul_centralScalar_le_eight_mul_scale_of_nonempty
    ht hgeometry hnonempty
  have hyC :=
    Complex.sharpFrequencyScalar_mul_crossingScalar_le_two_thirds_scale
      hgeometry
  have hyL :=
    Complex.sharpFrequencyScalar_mul_tailScalar_le_two_scale ht hgeometry
  have hyM :=
    Complex.sharpFrequencyScalar_mul_centralScalar_le_two_scale hgeometry
  have hcomponents := Real.add_two_four_term_bounds
    hxC hxL hxM hxL hyC hyL hyM hyL
  have hweighted :
      (3 * S + 8 * S + 8 * S + 8 * S) +
          ((2 / 3) * S + 2 * S + 2 * S + 2 * S) =
        (101 / 3) * S := by
    have hfactor := Real.two_four_weighted_terms_eq_sum_coeff_mul
      3 8 8 8 (2 / 3) 2 2 2 S
    exact hfactor.trans
      (congrArg (fun coefficient : ℝ => coefficient * S)
        Real.sharp_frequency_active_coefficient_sum_eq_one_hundred_one_thirds)
  have hcoefficient : (101 / 3 : ℝ) ≤ 34 := by
    have hthreePos : (0 : ℝ) < 3 :=
      Nat.cast_pos.mpr (Nat.succ_pos 2)
    have hproduct : (34 : ℝ) * 3 = 102 :=
      realOfNat_mul_eq_of_nat_eq 34 3 102 rfl
    have hbound : (101 : ℝ) ≤ 102 :=
      Nat.cast_le.mpr (Nat.le_succ 101)
    exact (div_le_iff₀ hthreePos).mpr
      (Eq.subst (motive := fun value : ℝ => 101 ≤ value)
        hproduct.symm hbound)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient
    (Complex.logarithmicPhaseBProcessScale_nonneg t)
  exact Eq.subst (motive := fun value : ℝ => value ≤ 34 * S)
    hexpand.symm
    (le_trans hcomponents (le_trans (le_of_eq hweighted) henlarge))

end

end LFunctions
end Boundary
