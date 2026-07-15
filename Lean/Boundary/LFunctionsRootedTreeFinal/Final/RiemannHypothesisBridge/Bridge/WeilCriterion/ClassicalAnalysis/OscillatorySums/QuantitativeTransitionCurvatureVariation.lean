import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionSymmetry

/-!
# Total curvature variation of the quantitative transition

This owner converts the half-interval signs of the second derivative into an
exact total-variation identity for the first derivative.  The sign theorem is
proved in the adjacent analytic owner; the calculus and constant arithmetic
live here.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

theorem Real.continuous_smoothTransitionDerivative :
    Continuous Real.smoothTransitionDerivative := by
  have hdifferentiable :
      Differentiable ℝ Real.smoothTransitionDerivative :=
    fun x => (Real.hasDerivAt_smoothTransitionDerivative x).differentiableAt
  exact hdifferentiable.continuous

theorem Real.continuous_smoothTransitionSecondDerivative :
    Continuous Real.smoothTransitionSecondDerivative := by
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransition :=
    Real.smoothTransition.contDiff
  have hfirstRaw : ContDiff ℝ (⊤ : ℕ∞) (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.mp hsmooth).2
  have hfirstFunction :
      deriv Real.smoothTransition = Real.smoothTransitionDerivative := by
    funext x
    exact Real.deriv_smoothTransition_exact x
  have hfirst : ContDiff ℝ (⊤ : ℕ∞) Real.smoothTransitionDerivative :=
    Eq.subst
      (motive := fun function : ℝ → ℝ =>
        ContDiff ℝ (⊤ : ℕ∞) function)
      hfirstFunction
      hfirstRaw
  have hsecondRaw : Continuous (deriv Real.smoothTransitionDerivative) :=
    (contDiff_infty_iff_deriv.mp hfirst).2.continuous
  have hsecondFunction :
      deriv Real.smoothTransitionDerivative =
        Real.smoothTransitionSecondDerivative := by
    funext x
    exact Real.deriv_smoothTransitionDerivative x
  exact Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hsecondFunction
    hsecondRaw

theorem Real.intervalIntegrable_smoothTransitionSecondDerivative
    (left right : ℝ) :
    IntervalIntegrable Real.smoothTransitionSecondDerivative
      volume left right := by
  exact Real.continuous_smoothTransitionSecondDerivative.intervalIntegrable
    left right

theorem Real.intervalIntegrable_abs_smoothTransitionSecondDerivative
    (left right : ℝ) :
    IntervalIntegrable
      (fun x : ℝ => |Real.smoothTransitionSecondDerivative x|)
      volume left right := by
  exact Real.continuous_smoothTransitionSecondDerivative.abs.intervalIntegrable
    left right

theorem Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
    (left right : ℝ) :
    (∫ x in left..right, Real.smoothTransitionSecondDerivative x) =
      Real.smoothTransitionDerivative right -
        Real.smoothTransitionDerivative left := by
  have hderiv :
      ∀ x ∈ Set.uIcc left right,
        DifferentiableAt ℝ Real.smoothTransitionDerivative x :=
    fun x hx =>
      (Real.hasDerivAt_smoothTransitionDerivative x).differentiableAt
  have hintegrable :
      IntervalIntegrable (deriv Real.smoothTransitionDerivative)
        volume left right := by
    have hsecondIntegrable :
        IntervalIntegrable Real.smoothTransitionSecondDerivative
          volume left right :=
      Real.intervalIntegrable_smoothTransitionSecondDerivative left right
    have hfunction :
        deriv Real.smoothTransitionDerivative =
          Real.smoothTransitionSecondDerivative := by
      funext x
      exact Real.deriv_smoothTransitionDerivative x
    exact Eq.subst
      (motive := fun function : ℝ → ℝ =>
        IntervalIntegrable function volume left right)
      hfunction.symm
      hsecondIntegrable
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hintegrable
  have hintegrand :
      (∫ x in left..right, deriv Real.smoothTransitionDerivative x) =
        ∫ x in left..right, Real.smoothTransitionSecondDerivative x :=
    intervalIntegral.integral_congr
      (fun x hx => Real.deriv_smoothTransitionDerivative x)
  exact hintegrand.symm.trans hftc

theorem Real.abs_smoothTransitionSecondDerivative_eq_self_of_nonneg
    {x : ℝ}
    (hx : 0 ≤ Real.smoothTransitionSecondDerivative x) :
    |Real.smoothTransitionSecondDerivative x| =
      Real.smoothTransitionSecondDerivative x := by
  exact abs_of_nonneg hx

theorem Real.abs_smoothTransitionSecondDerivative_eq_neg_of_nonpos
    {x : ℝ}
    (hx : Real.smoothTransitionSecondDerivative x ≤ 0) :
    |Real.smoothTransitionSecondDerivative x| =
      -Real.smoothTransitionSecondDerivative x := by
  exact abs_of_nonpos hx

theorem Real.integral_abs_smoothTransitionSecondDerivative_left_half
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x) :
    (∫ x in (0 : ℝ)..(1 / 2),
      |Real.smoothTransitionSecondDerivative x|) =
      Real.smoothTransitionDerivative (1 / 2) -
        Real.smoothTransitionDerivative 0 := by
  have hhalfNonneg : (0 : ℝ) ≤ 1 / 2 :=
    one_div_nonneg.mpr (Nat.cast_nonneg 2)
  have huIcc : Set.uIcc (0 : ℝ) (1 / 2) = Set.Icc 0 (1 / 2) :=
    Set.uIcc_of_le hhalfNonneg
  have hintegrand :
      (∫ x in (0 : ℝ)..(1 / 2),
        |Real.smoothTransitionSecondDerivative x|) =
        ∫ x in (0 : ℝ)..(1 / 2),
          Real.smoothTransitionSecondDerivative x :=
    intervalIntegral.integral_congr
      (fun x hx =>
        Real.abs_smoothTransitionSecondDerivative_eq_self_of_nonneg
          (hleft x
            (Eq.subst
              (motive := fun interval : Set ℝ => x ∈ interval)
              huIcc
              hx)))
  exact hintegrand.trans
    (Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
      0 (1 / 2))

theorem Real.integral_abs_smoothTransitionSecondDerivative_right_half
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (1 / 2 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) =
      Real.smoothTransitionDerivative (1 / 2) -
        Real.smoothTransitionDerivative 1 := by
  have hhalfLeOne : (1 / 2 : ℝ) ≤ 1 := by
    have honeLeTwo : (1 : ℝ) ≤ 2 := one_le_two
    have hraw : (1 / 2 : ℝ) ≤ 1 / 1 :=
      one_div_le_one_div_of_le zero_lt_one honeLeTwo
    exact le_trans hraw (le_of_eq (div_one 1))
  have huIcc : Set.uIcc (1 / 2 : ℝ) 1 = Set.Icc (1 / 2) 1 :=
    Set.uIcc_of_le hhalfLeOne
  have hintegrand :
      (∫ x in (1 / 2 : ℝ)..1,
        |Real.smoothTransitionSecondDerivative x|) =
        ∫ x in (1 / 2 : ℝ)..1,
          -Real.smoothTransitionSecondDerivative x :=
    intervalIntegral.integral_congr
      (fun x hx =>
        Real.abs_smoothTransitionSecondDerivative_eq_neg_of_nonpos
          (hright x
            (Eq.subst
              (motive := fun interval : Set ℝ => x ∈ interval)
              huIcc
              hx)))
  have hnegative :
      (∫ x in (1 / 2 : ℝ)..1,
        -Real.smoothTransitionSecondDerivative x) =
        -(∫ x in (1 / 2 : ℝ)..1,
          Real.smoothTransitionSecondDerivative x) :=
    intervalIntegral.integral_neg
  have hftc :=
    Real.integral_smoothTransitionSecondDerivative_eq_derivative_sub
      (1 / 2) 1
  have hnormalize :
      -(Real.smoothTransitionDerivative 1 -
          Real.smoothTransitionDerivative (1 / 2)) =
        Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 1 := by
    exact neg_sub _ _
  exact hintegrand.trans
    (hnegative.trans
      ((congrArg Neg.neg hftc).trans hnormalize))

theorem Real.smoothTransition_half_complement :
    (1 : ℝ) - 1 / 2 = 1 / 2 := by
  have htwoNe : (2 : ℝ) ≠ 0 := two_ne_zero
  have honeAsHalf : (1 : ℝ) = 2 / 2 := (div_self htwoNe).symm
  calc
    (1 : ℝ) - 1 / 2 = 2 / 2 - 1 / 2 :=
      congrArg (fun value : ℝ => value - 1 / 2) honeAsHalf
    _ = (2 - 1) / 2 := (sub_div 2 1 2).symm
    _ = 1 / 2 :=
      congrArg (fun value : ℝ => value / 2) Real.two_sub_one_eq_one

theorem Real.smoothTransition_half_inverse :
    (1 / 2 : ℝ)⁻¹ = 2 := by
  have honeDiv : (1 / 2 : ℝ) = (2 : ℝ)⁻¹ := one_div 2
  exact (congrArg Inv.inv honeDiv).trans (inv_inv 2)

theorem Real.smoothTransition_two_sq_eq_four :
    (2 : ℝ) ^ 2 = 4 := by
  exact (pow_two (2 : ℝ)).trans
    (Real.transitionSecondDerivative_natCast_mul 2 2 4 rfl)

theorem Real.expNegInvGlueDerivative_half_eq_four_mul :
    Real.expNegInvGlueDerivative (1 / 2) =
      4 * expNegInvGlue (1 / 2) := by
  have hinverseSquare : (1 / 2 : ℝ)⁻¹ ^ 2 = 4 :=
    (congrArg (fun value : ℝ => value ^ 2)
      Real.smoothTransition_half_inverse).trans
      Real.smoothTransition_two_sq_eq_four
  exact (Real.expNegInvGlueDerivative_eq_inv_sq_mul (1 / 2)).trans
    (congrArg (fun value : ℝ => value * expNegInvGlue (1 / 2))
      hinverseSquare)

theorem Real.smoothTransitionDerivativeNumerator_half_eq_eight_mul_sq :
    Real.smoothTransitionDerivativeNumerator (1 / 2) =
      8 * expNegInvGlue (1 / 2) ^ 2 := by
  let g := expNegInvGlue (1 / 2)
  have hcomplement := Real.smoothTransition_half_complement
  have hglueComplement : expNegInvGlue (1 - 1 / 2) = g :=
    congrArg expNegInvGlue hcomplement
  have hderivativeComplement :
      Real.expNegInvGlueDerivative (1 - 1 / 2) =
        Real.expNegInvGlueDerivative (1 / 2) :=
    congrArg Real.expNegInvGlueDerivative hcomplement
  have hderivative :
      Real.expNegInvGlueDerivative (1 / 2) = 4 * g :=
    Real.expNegInvGlueDerivative_half_eq_four_mul
  have hfourAddFour : (4 : ℝ) + 4 = 8 :=
    Real.transitionSecondDerivative_natCast_add 4 4 8 rfl
  unfold Real.smoothTransitionDerivativeNumerator
  change
    Real.expNegInvGlueDerivative (1 / 2) *
        expNegInvGlue (1 - 1 / 2) +
      expNegInvGlue (1 / 2) *
        Real.expNegInvGlueDerivative (1 - 1 / 2) =
      8 * g ^ 2
  calc
    Real.expNegInvGlueDerivative (1 / 2) *
          expNegInvGlue (1 - 1 / 2) +
        expNegInvGlue (1 / 2) *
          Real.expNegInvGlueDerivative (1 - 1 / 2) =
      Real.expNegInvGlueDerivative (1 / 2) * g +
        g * Real.expNegInvGlueDerivative (1 / 2) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (congrArg
          (fun value : ℝ =>
            Real.expNegInvGlueDerivative (1 / 2) * value)
          hglueComplement)
        (congrArg (fun value : ℝ => g * value) hderivativeComplement)
    _ = (4 * g) * g + g * (4 * g) :=
      congrArg₂ (fun first second : ℝ => first * g + g * second)
        hderivative hderivative
    _ = 4 * (g * g) + 4 * (g * g) :=
      congrArg₂ (fun first second : ℝ => first + second)
        (mul_assoc 4 g g)
        ((mul_assoc g 4 g).symm.trans
          ((congrArg (fun value : ℝ => value * g) (mul_comm g 4)).trans
            (mul_assoc 4 g g)))
    _ = (4 + 4) * (g * g) := (add_mul 4 4 (g * g)).symm
    _ = 8 * (g * g) :=
      congrArg (fun value : ℝ => value * (g * g)) hfourAddFour
    _ = 8 * g ^ 2 :=
      congrArg (fun value : ℝ => 8 * value) (pow_two g).symm

theorem Real.smoothTransitionDerivativeDenominator_half_sq_eq_four_mul_sq :
    Real.smoothTransitionDerivativeDenominator (1 / 2) ^ 2 =
      4 * expNegInvGlue (1 / 2) ^ 2 := by
  let g := expNegInvGlue (1 / 2)
  have hglueComplement : expNegInvGlue (1 - 1 / 2) = g :=
    congrArg expNegInvGlue Real.smoothTransition_half_complement
  have hdenominator :
      Real.smoothTransitionDerivativeDenominator (1 / 2) = 2 * g := by
    unfold Real.smoothTransitionDerivativeDenominator
    exact (congrArg (fun value : ℝ => g + value) hglueComplement).trans
      (two_mul g).symm
  calc
    Real.smoothTransitionDerivativeDenominator (1 / 2) ^ 2 =
        (2 * g) ^ 2 := congrArg (fun value : ℝ => value ^ 2) hdenominator
    _ = 2 ^ 2 * g ^ 2 := mul_pow 2 g 2
    _ = 4 * g ^ 2 :=
      congrArg (fun value : ℝ => value * g ^ 2)
        Real.smoothTransition_two_sq_eq_four

theorem Real.smoothTransitionDerivative_half_eq_two :
    Real.smoothTransitionDerivative (1 / 2) = 2 := by
  let g := expNegInvGlue (1 / 2)
  have hdenominatorSq :=
    Real.smoothTransitionDerivativeDenominator_half_sq_eq_four_mul_sq
  have hdenominatorPos :
      0 < Real.smoothTransitionDerivativeDenominator (1 / 2) := by
    unfold Real.smoothTransitionDerivativeDenominator
    exact Real.smoothTransitionDenominator_pos (1 / 2)
  have hdenominatorSqNe :
      Real.smoothTransitionDerivativeDenominator (1 / 2) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt hdenominatorPos)
  have hnumerator :=
    Real.smoothTransitionDerivativeNumerator_half_eq_eight_mul_sq
  have htwoMulFour : (2 : ℝ) * 4 = 8 :=
    Real.transitionSecondDerivative_natCast_mul 2 4 8 rfl
  have hquotientNumerator :
      Real.smoothTransitionDerivativeNumerator (1 / 2) =
        2 * Real.smoothTransitionDerivativeDenominator (1 / 2) ^ 2 := by
    calc
      Real.smoothTransitionDerivativeNumerator (1 / 2) = 8 * g ^ 2 :=
        hnumerator
      _ = (2 * 4) * g ^ 2 :=
        congrArg (fun value : ℝ => value * g ^ 2) htwoMulFour.symm
      _ = 2 * (4 * g ^ 2) := mul_assoc 2 4 (g ^ 2)
      _ = 2 * Real.smoothTransitionDerivativeDenominator (1 / 2) ^ 2 :=
        congrArg (fun value : ℝ => 2 * value) hdenominatorSq.symm
  exact (Real.smoothTransitionDerivative_eq_normalized (1 / 2)).trans
    ((div_eq_iff hdenominatorSqNe).2 hquotientNumerator)

theorem Real.smoothTransitionDerivative_half_le_four :
    Real.smoothTransitionDerivative (1 / 2) ≤ 4 := by
  have htwoLeSum : (2 : ℝ) ≤ 2 + 2 :=
    le_add_of_nonneg_right (Nat.cast_nonneg 2)
  have htwoAddTwo : (2 : ℝ) + 2 = 4 :=
    Real.transitionSecondDerivative_natCast_add 2 2 4 rfl
  have htwoLeFour : (2 : ℝ) ≤ 4 :=
    le_trans htwoLeSum (le_of_eq htwoAddTwo)
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 4)
    Real.smoothTransitionDerivative_half_eq_two.symm
    htwoLeFour

theorem Real.integral_abs_smoothTransitionSecondDerivative_eq_twice_midpoint
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x)
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (0 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) =
      2 * Real.smoothTransitionDerivative (1 / 2) := by
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (Real.intervalIntegrable_abs_smoothTransitionSecondDerivative 0 (1 / 2))
    (Real.intervalIntegrable_abs_smoothTransitionSecondDerivative (1 / 2) 1)
  have hleftIntegral :=
    Real.integral_abs_smoothTransitionSecondDerivative_left_half hleft
  have hrightIntegral :=
    Real.integral_abs_smoothTransitionSecondDerivative_right_half hright
  have hnormalize :
      (Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 0) +
        (Real.smoothTransitionDerivative (1 / 2) -
          Real.smoothTransitionDerivative 1) =
        2 * Real.smoothTransitionDerivative (1 / 2) := by
    exact Eq.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg
          (fun endpoint : ℝ =>
            Real.smoothTransitionDerivative (1 / 2) - endpoint)
          Real.smoothTransitionDerivative_zero)
        (congrArg
          (fun endpoint : ℝ =>
            Real.smoothTransitionDerivative (1 / 2) - endpoint)
          Real.smoothTransitionDerivative_one))
      (Eq.trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (sub_zero _) (sub_zero _))
        (two_mul _).symm)
  exact hsplit.symm.trans
    ((congrArg₂ (fun first second : ℝ => first + second)
      hleftIntegral hrightIntegral).trans hnormalize)

theorem Real.integral_abs_smoothTransitionSecondDerivative_le_eight
    (hleft :
      ∀ x ∈ Set.Icc (0 : ℝ) (1 / 2),
        0 ≤ Real.smoothTransitionSecondDerivative x)
    (hright :
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1,
        Real.smoothTransitionSecondDerivative x ≤ 0) :
    (∫ x in (0 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) ≤ 8 := by
  have hidentity :=
    Real.integral_abs_smoothTransitionSecondDerivative_eq_twice_midpoint
      hleft hright
  have hmidpoint := Real.smoothTransitionDerivative_half_le_four
  have hdouble := mul_le_mul_of_nonneg_left hmidpoint (Nat.cast_nonneg 2)
  have hnormalize : (2 : ℝ) * 4 = 8 :=
    Real.transitionSecondDerivative_natCast_mul 2 4 8 rfl
  exact Eq.subst
    (motive := fun integralValue : ℝ => integralValue ≤ 8)
    hidentity.symm
    (le_trans hdouble (le_of_eq hnormalize))

end
end LFunctions
end Boundary
