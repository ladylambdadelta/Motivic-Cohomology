import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionMonotonicity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeMassBounds

/-!
# Uniform variation bound for the quantitative block cutoff

The increasing collar has total variation one and the decreasing collar has
total variation one.  The product cutoff therefore has total variation at
most two, uniformly in the integer block endpoints.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

theorem Real.quantitativeLogarithmicLeftCutoff_at_blockSupportRight
    (a b : ℤ)
    (hab : a ≤ b) :
    Real.quantitativeLogarithmicLeftCutoff a
        (Complex.logarithmicPhaseQuantitativeSupportRight b) = 1 := by
  unfold Complex.logarithmicPhaseQuantitativeSupportRight
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  exact Real.quantitativeLogarithmicLeftCutoff_eq_one_of_le
    (le_trans habReal (le_add_of_nonneg_right hthirdNonneg))

theorem Real.quantitativeLogarithmicRightCutoff_at_blockSupportLeft
    (a b : ℤ)
    (hab : a ≤ b) :
    Real.quantitativeLogarithmicRightCutoff b
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) = 1 := by
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 := le_of_lt Real.one_div_three_pos
  have hleft : (a : ℝ) - 1 / 3 ≤ (a : ℝ) :=
    sub_le_self (a : ℝ) hthirdNonneg
  exact Real.quantitativeLogarithmicRightCutoff_eq_one_of_le
    (le_trans hleft habReal)

theorem Real.intervalIntegrable_quantitativeLogarithmicLeftCutoffDerivative
    (a : ℤ) (left right : ℝ) :
    IntervalIntegrable
      (Real.quantitativeLogarithmicLeftCutoffDerivative a)
      volume left right := by
  have hderivative :=
    (contDiff_infty_iff_deriv.mp
      (Real.contDiff_quantitativeLogarithmicLeftCutoff a)).2.continuous
  have hfunction :
      deriv (Real.quantitativeLogarithmicLeftCutoff a) =
        Real.quantitativeLogarithmicLeftCutoffDerivative a := by
    funext x
    exact Real.deriv_quantitativeLogarithmicLeftCutoff a x
  have hcontinuous := Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hfunction hderivative
  exact hcontinuous.intervalIntegrable left right

theorem Real.intervalIntegrable_quantitativeLogarithmicRightCutoffDerivative
    (b : ℤ) (left right : ℝ) :
    IntervalIntegrable
      (Real.quantitativeLogarithmicRightCutoffDerivative b)
      volume left right := by
  have hderivative :=
    (contDiff_infty_iff_deriv.mp
      (Real.contDiff_quantitativeLogarithmicRightCutoff b)).2.continuous
  have hfunction :
      deriv (Real.quantitativeLogarithmicRightCutoff b) =
        Real.quantitativeLogarithmicRightCutoffDerivative b := by
    funext x
    exact Real.deriv_quantitativeLogarithmicRightCutoff b x
  have hcontinuous := Eq.subst
    (motive := fun function : ℝ → ℝ => Continuous function)
    hfunction hderivative
  exact hcontinuous.intervalIntegrable left right

theorem Real.integral_quantitativeLogarithmicLeftCutoffDerivative_eq_one
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Real.quantitativeLogarithmicLeftCutoffDerivative a x) = 1 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hderiv :
      ∀ x ∈ [[left, right]],
        DifferentiableAt ℝ (Real.quantitativeLogarithmicLeftCutoff a) x :=
    fun x hx =>
      (Real.hasDerivAt_quantitativeLogarithmicLeftCutoff a x).differentiableAt
  have hintegrable : IntervalIntegrable
      (deriv (Real.quantitativeLogarithmicLeftCutoff a))
      volume left right := by
    have hcontinuous :=
      (Real.contDiff_quantitativeLogarithmicLeftCutoff a).continuous
    have hderivativeContinuous :=
      (contDiff_infty_iff_deriv.mp
        (Real.contDiff_quantitativeLogarithmicLeftCutoff a)).2.continuous
    exact hderivativeContinuous.intervalIntegrable left right
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hintegrable
  have hderivativeIntegral :
      (∫ x in left..right,
        Real.quantitativeLogarithmicLeftCutoffDerivative a x) =
        Real.quantitativeLogarithmicLeftCutoff a right -
          Real.quantitativeLogarithmicLeftCutoff a left := by
    have hintegrand :
        (∫ x in left..right,
          deriv (Real.quantitativeLogarithmicLeftCutoff a) x) =
          ∫ x in left..right,
            Real.quantitativeLogarithmicLeftCutoffDerivative a x :=
      intervalIntegral.integral_congr
        (fun x hx => Real.deriv_quantitativeLogarithmicLeftCutoff a x)
    exact hintegrand.symm.trans hftc
  have hright :=
    Real.quantitativeLogarithmicLeftCutoff_at_blockSupportRight a b hab
  have hleft := Real.quantitativeLogarithmicLeftCutoff_at_supportLeft a
  exact hderivativeIntegral.trans
    ((congrArg₂ (fun first second : ℝ => first - second)
      hright hleft).trans (sub_zero 1))

theorem Real.integral_abs_quantitativeLogarithmicLeftCutoffDerivative_eq_one
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicLeftCutoffDerivative a x|) = 1 := by
  have hintegrand :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        |Real.quantitativeLogarithmicLeftCutoffDerivative a x|) =
        ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
          Real.quantitativeLogarithmicLeftCutoffDerivative a x :=
    intervalIntegral.integral_congr
      (fun x hx => Real.abs_quantitativeLogarithmicLeftCutoffDerivative a x)
  exact hintegrand.trans
    (Real.integral_quantitativeLogarithmicLeftCutoffDerivative_eq_one a b hab)

theorem Real.integral_quantitativeLogarithmicRightCutoffDerivative_eq_neg_one
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      Real.quantitativeLogarithmicRightCutoffDerivative b x) = -1 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hderiv :
      ∀ x ∈ [[left, right]],
        DifferentiableAt ℝ (Real.quantitativeLogarithmicRightCutoff b) x :=
    fun x hx =>
      (Real.hasDerivAt_quantitativeLogarithmicRightCutoff b x).differentiableAt
  have hintegrable : IntervalIntegrable
      (deriv (Real.quantitativeLogarithmicRightCutoff b))
      volume left right := by
    have hderivativeContinuous : Continuous
        (deriv (Real.quantitativeLogarithmicRightCutoff b)) :=
      (contDiff_infty_iff_deriv.mp
        (Real.contDiff_quantitativeLogarithmicRightCutoff b)).2.continuous
    exact hderivativeContinuous.intervalIntegrable left right
  have hftc := intervalIntegral.integral_deriv_eq_sub hderiv hintegrable
  have hintegrand :
      (∫ x in left..right,
        deriv (Real.quantitativeLogarithmicRightCutoff b) x) =
        ∫ x in left..right,
          Real.quantitativeLogarithmicRightCutoffDerivative b x :=
    intervalIntegral.integral_congr
      (fun x hx => Real.deriv_quantitativeLogarithmicRightCutoff b x)
  have hright := Real.quantitativeLogarithmicRightCutoff_at_supportRight b
  have hleft :=
    Real.quantitativeLogarithmicRightCutoff_at_blockSupportLeft a b hab
  exact (hintegrand.symm.trans hftc).trans
    ((congrArg₂ (fun first second : ℝ => first - second)
      hright hleft).trans (zero_sub 1))

theorem Real.integral_abs_quantitativeLogarithmicRightCutoffDerivative_eq_one
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicRightCutoffDerivative b x|) = 1 := by
  have hintegrand :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        |Real.quantitativeLogarithmicRightCutoffDerivative b x|) =
        ∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
          -Real.quantitativeLogarithmicRightCutoffDerivative b x :=
    intervalIntegral.integral_congr
      (fun x hx => Real.abs_quantitativeLogarithmicRightCutoffDerivative b x)
  have hnegative :
      (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
        -Real.quantitativeLogarithmicRightCutoffDerivative b x) =
        -(∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
          Complex.logarithmicPhaseQuantitativeSupportRight b,
          Real.quantitativeLogarithmicRightCutoffDerivative b x) :=
    intervalIntegral.integral_neg
  have hintegral :=
    Real.integral_quantitativeLogarithmicRightCutoffDerivative_eq_neg_one
      a b hab
  exact hintegrand.trans
    (hnegative.trans
      ((congrArg Neg.neg hintegral).trans (neg_neg 1)))

theorem Real.abs_quantitativeLogarithmicBlockCutoffDerivative_le_sum
    (a b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicBlockCutoffDerivative a b x| ≤
      |Real.quantitativeLogarithmicLeftCutoffDerivative a x| +
        |Real.quantitativeLogarithmicRightCutoffDerivative b x| := by
  unfold Real.quantitativeLogarithmicBlockCutoffDerivative
  have htriangle := abs_add
    (Real.quantitativeLogarithmicLeftCutoffDerivative a x *
      Real.quantitativeLogarithmicRightCutoff b x)
    (Real.quantitativeLogarithmicLeftCutoff a x *
      Real.quantitativeLogarithmicRightCutoffDerivative b x)
  have hrightNorm :
      |Real.quantitativeLogarithmicRightCutoff b x| ≤ 1 := by
    exact (abs_of_nonneg
      (Real.quantitativeLogarithmicRightCutoff_nonneg b x)).trans_le
      (Real.quantitativeLogarithmicRightCutoff_le_one b x)
  have hleftNorm :
      |Real.quantitativeLogarithmicLeftCutoff a x| ≤ 1 := by
    exact (abs_of_nonneg
      (Real.quantitativeLogarithmicLeftCutoff_nonneg a x)).trans_le
      (Real.quantitativeLogarithmicLeftCutoff_le_one a x)
  have hfirst :
      |Real.quantitativeLogarithmicLeftCutoffDerivative a x *
          Real.quantitativeLogarithmicRightCutoff b x| ≤
        |Real.quantitativeLogarithmicLeftCutoffDerivative a x| := by
    have hproduct := abs_mul
      (Real.quantitativeLogarithmicLeftCutoffDerivative a x)
      (Real.quantitativeLogarithmicRightCutoff b x)
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul_of_nonneg_left hrightNorm (abs_nonneg _))
        (le_of_eq (mul_one _)))
  have hsecond :
      |Real.quantitativeLogarithmicLeftCutoff a x *
          Real.quantitativeLogarithmicRightCutoffDerivative b x| ≤
        |Real.quantitativeLogarithmicRightCutoffDerivative b x| := by
    have hproduct := abs_mul
      (Real.quantitativeLogarithmicLeftCutoff a x)
      (Real.quantitativeLogarithmicRightCutoffDerivative b x)
    exact le_trans (le_of_eq hproduct)
      (le_trans
        (mul_le_mul_of_nonneg_right hleftNorm (abs_nonneg _))
        (le_of_eq (one_mul _)))
  exact le_trans htriangle (add_le_add hfirst hsecond)

theorem Complex.logarithmicPhaseQuantitativeCutoffVariationMass_le_two
    (a b : ℤ)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeCutoffVariationMass a b ≤ 2 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hblock : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicBlockCutoffDerivative a b x|)
      volume left right := by
    have hcontinuous : Continuous
        (Real.quantitativeLogarithmicBlockCutoffDerivative a b) :=
      (Real.contDiff_quantitativeLogarithmicBlockCutoffDerivative a b).continuous
    exact hcontinuous.abs.intervalIntegrable left right
  have hsum : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffDerivative a x| +
          |Real.quantitativeLogarithmicRightCutoffDerivative b x|)
      volume left right :=
    (Real.intervalIntegrable_quantitativeLogarithmicLeftCutoffDerivative
      a left right).abs.add
      (Real.intervalIntegrable_quantitativeLogarithmicRightCutoffDerivative
        b left right).abs
  have hmono := intervalIntegral.integral_mono_on hleftRight hblock hsum
    (fun x hx =>
      Real.abs_quantitativeLogarithmicBlockCutoffDerivative_le_sum a b x)
  have hadd := intervalIntegral.integral_add
    (Real.intervalIntegrable_quantitativeLogarithmicLeftCutoffDerivative
      a left right).abs
    (Real.intervalIntegrable_quantitativeLogarithmicRightCutoffDerivative
      b left right).abs
  have hleftIntegral :=
    Real.integral_abs_quantitativeLogarithmicLeftCutoffDerivative_eq_one
      a b hab
  have hrightIntegral :=
    Real.integral_abs_quantitativeLogarithmicRightCutoffDerivative_eq_one
      a b hab
  have hsumValue :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffDerivative a x| +
          |Real.quantitativeLogarithmicRightCutoffDerivative b x|) = 2 :=
    hadd.trans
      ((congrArg₂ (fun first second : ℝ => first + second)
        hleftIntegral hrightIntegral).trans one_add_one_eq_two)
  unfold Complex.logarithmicPhaseQuantitativeCutoffVariationMass
  exact le_trans hmono (le_of_eq hsumValue)

end
end LFunctions
end Boundary
