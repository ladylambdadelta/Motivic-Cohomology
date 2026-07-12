import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionConvexity
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCutoffCurvatureMassBound

/-!
# Sharp curvature mass for the quantitative logarithmic cutoff

Affine substitution converts each width-one-third collar into the unit
transition interval.  The factor `9` in the second derivative and Jacobian
`1/3` leave a factor `3`; the transition variation bound `8` therefore gives
`24` per collar and `48` for the block cutoff.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Real.quantitativeLogarithmicSharpCollarCurvatureMassBound : ℝ := 24

def Real.quantitativeLogarithmicSharpBlockCurvatureMassBound : ℝ := 48

theorem Real.quantitativeLogarithmicSharpCollarCurvatureMassBound_nonneg :
    0 ≤ Real.quantitativeLogarithmicSharpCollarCurvatureMassBound := by
  unfold Real.quantitativeLogarithmicSharpCollarCurvatureMassBound
  exact Nat.cast_nonneg 24

theorem Real.quantitativeLogarithmicSharpBlockCurvatureMassBound_nonneg :
    0 ≤ Real.quantitativeLogarithmicSharpBlockCurvatureMassBound := by
  unfold Real.quantitativeLogarithmicSharpBlockCurvatureMassBound
  exact Nat.cast_nonneg 48

theorem Real.abs_leftCutoffSecondDerivative_eq_nine_mul_transition
    (a : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| =
      9 * |Real.smoothTransitionSecondDerivative
        (3 * (x - (a : ℝ)) + 1)| := by
  unfold Real.quantitativeLogarithmicLeftCutoffSecondDerivative
  exact Eq.trans
    (abs_mul 9 _)
    (congrArg
      (fun coefficient : ℝ => coefficient *
        |Real.smoothTransitionSecondDerivative
          (3 * (x - (a : ℝ)) + 1)|)
      (abs_of_nonneg (Nat.cast_nonneg 9)))

theorem Real.abs_rightCutoffSecondDerivative_eq_nine_mul_transition
    (b : ℤ) (x : ℝ) :
    |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| =
      9 * |Real.smoothTransitionSecondDerivative
        (3 * ((b : ℝ) - x) + 1)| := by
  unfold Real.quantitativeLogarithmicRightCutoffSecondDerivative
  exact Eq.trans
    (abs_mul 9 _)
    (congrArg
      (fun coefficient : ℝ => coefficient *
        |Real.smoothTransitionSecondDerivative
          (3 * ((b : ℝ) - x) + 1)|)
      (abs_of_nonneg (Nat.cast_nonneg 9)))

theorem Real.leftCollar_affine_argument_eq
    (a : ℤ) (x : ℝ) :
    3 * (x - (a : ℝ)) + 1 =
      3 * x + (1 - 3 * (a : ℝ)) := by
  calc
    3 * (x - (a : ℝ)) + 1 =
        (3 * x - 3 * (a : ℝ)) + 1 :=
      congrArg (fun value : ℝ => value + 1) (mul_sub 3 x (a : ℝ))
    _ = 3 * x + (-3 * (a : ℝ) + 1) :=
      add_assoc (3 * x) (-3 * (a : ℝ)) 1
    _ = 3 * x + (1 + -3 * (a : ℝ)) :=
      congrArg (fun value : ℝ => 3 * x + value)
        (add_comm (-3 * (a : ℝ)) 1)
    _ = 3 * x + (1 - 3 * (a : ℝ)) :=
      congrArg (fun value : ℝ => 3 * x + value)
        (sub_eq_add_neg 1 (3 * (a : ℝ))).symm

theorem Real.rightCollar_affine_argument_eq
    (b : ℤ) (x : ℝ) :
    3 * ((b : ℝ) - x) + 1 =
      (-3) * x + (1 + 3 * (b : ℝ)) := by
  calc
    3 * ((b : ℝ) - x) + 1 =
        (3 * (b : ℝ) - 3 * x) + 1 :=
      congrArg (fun value : ℝ => value + 1) (mul_sub 3 (b : ℝ) x)
    _ = (-3) * x + (3 * (b : ℝ) + 1) := by
      exact (add_assoc (3 * (b : ℝ)) (-(3 * x)) 1).trans
        (congrArg (fun value : ℝ => value + 1)
          (add_comm (3 * (b : ℝ)) (-(3 * x)))).trans
        (add_assoc (-(3 * x)) (3 * (b : ℝ)) 1).symm.trans
        (congrArg (fun value : ℝ => value + (3 * (b : ℝ) + 1))
          (neg_mul 3 x).symm)
    _ = (-3) * x + (1 + 3 * (b : ℝ)) :=
      congrArg (fun value : ℝ => (-3) * x + value)
        (add_comm (3 * (b : ℝ)) 1)

theorem Real.leftCollar_affine_left_endpoint
    (a : ℤ) :
    3 * ((a : ℝ) - 1 / 3) + (1 - 3 * (a : ℝ)) = 0 := by
  have hthreeNe : (3 : ℝ) ≠ 0 := three_ne_zero
  calc
    3 * ((a : ℝ) - 1 / 3) + (1 - 3 * (a : ℝ)) =
        (3 * (a : ℝ) - 3 * (1 / 3)) +
          (1 - 3 * (a : ℝ)) :=
      congrArg (fun value : ℝ => value + (1 - 3 * (a : ℝ)))
        (mul_sub 3 (a : ℝ) (1 / 3))
    _ = (3 * (a : ℝ) - 1) + (1 - 3 * (a : ℝ)) := by
      exact congrArg
        (fun value : ℝ => (3 * (a : ℝ) - value) +
          (1 - 3 * (a : ℝ)))
        (mul_one_div_cancel hthreeNe)
    _ = 0 := by
      exact add_neg_cancel (3 * (a : ℝ) - 1)

theorem Real.leftCollar_affine_right_endpoint
    (a : ℤ) :
    3 * (a : ℝ) + (1 - 3 * (a : ℝ)) = 1 := by
  exact add_sub_cancel_left (3 * (a : ℝ)) 1

theorem Real.rightCollar_affine_left_endpoint
    (b : ℤ) :
    (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) = 1 := by
  calc
    (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) =
        1 + ((-3) * (b : ℝ) + 3 * (b : ℝ)) := by
      exact (add_assoc ((-3) * (b : ℝ)) 1 (3 * (b : ℝ))).trans
        (add_comm ((-3) * (b : ℝ)) 1).trans
        (add_assoc 1 ((-3) * (b : ℝ)) (3 * (b : ℝ))).symm
    _ = 1 + 0 :=
      congrArg (fun value : ℝ => 1 + value)
        (neg_add_cancel (3 * (b : ℝ)))
    _ = 1 := add_zero 1

theorem Real.rightCollar_affine_right_endpoint
    (b : ℤ) :
    (-3) * ((b : ℝ) + 1 / 3) + (1 + 3 * (b : ℝ)) = 0 := by
  have hthreeNe : (3 : ℝ) ≠ 0 := three_ne_zero
  calc
    (-3) * ((b : ℝ) + 1 / 3) + (1 + 3 * (b : ℝ)) =
        ((-3) * (b : ℝ) + (-3) * (1 / 3)) +
          (1 + 3 * (b : ℝ)) :=
      congrArg (fun value : ℝ => value + (1 + 3 * (b : ℝ)))
        (mul_add (-3) (b : ℝ) (1 / 3))
    _ = ((-3) * (b : ℝ) + (-1)) +
          (1 + 3 * (b : ℝ)) := by
      congr 1
      exact congrArg Neg.neg (mul_one_div_cancel hthreeNe)
    _ = 0 := by
      have hfirst : (-3) * (b : ℝ) + (-1) =
          -(1 + 3 * (b : ℝ)) := by
        exact (neg_add_rev 1 (3 * (b : ℝ))).symm.trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (neg_mul 3 (b : ℝ)).symm rfl)
      exact Eq.trans
        (congrArg (fun value : ℝ => value + (1 + 3 * (b : ℝ))) hfirst)
        (neg_add_cancel (1 + 3 * (b : ℝ)))

theorem Real.integral_abs_leftCollarSecondDerivative_eq_three_mul_transition
    (a : ℤ) :
    (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
      3 * (∫ y in (0 : ℝ)..1,
        |Real.smoothTransitionSecondDerivative y|) := by
  let f : ℝ → ℝ := fun y => |Real.smoothTransitionSecondDerivative y|
  have hthreeNe : (3 : ℝ) ≠ 0 := three_ne_zero
  have hsubstitution := intervalIntegral.integral_comp_mul_add
    (f := f) (a := (a : ℝ) - 1 / 3) (b := (a : ℝ))
    hthreeNe (1 - 3 * (a : ℝ))
  have harguments := intervalIntegral.integral_congr
    (fun x hx => congrArg f (Real.leftCollar_affine_argument_eq a x).symm)
  have hendpoints := congrArg
    (fun leftRight : ℝ × ℝ =>
      (3 : ℝ)⁻¹ • ∫ y in leftRight.1..leftRight.2, f y)
    (Prod.ext
      (Real.leftCollar_affine_left_endpoint a)
      (Real.leftCollar_affine_right_endpoint a))
  have hscaled := congrArg (fun value : ℝ => 9 * value)
    (Eq.trans harguments hsubstitution)
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx => Real.abs_leftCutoffSecondDerivative_eq_nine_mul_transition a x)
  exact Eq.trans hintegrand
    (Eq.trans (intervalIntegral.integral_const_mul 9)
      (Eq.trans hscaled
        (by
          have hthird : (3 : ℝ)⁻¹ = 1 / 3 := rfl
          have hnineThird : 9 * (1 / 3 : ℝ) = 3 := by
            exact (mul_div_assoc 9 1 3).trans
              (Eq.trans (congrArg (fun value : ℝ => value / 3) (mul_one 9))
                (div_eq_iff₀ hthreeNe).2 rfl)
          exact Eq.trans
            (congrArg (fun coefficient : ℝ => coefficient *
              (∫ y in (0 : ℝ)..1, f y)) hnineThird)
            rfl)))

theorem Real.integral_abs_leftCollarSecondDerivative_le_twenty_four
    (a : ℤ) :
    (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤ 24 := by
  have hidentity :=
    Real.integral_abs_leftCollarSecondDerivative_eq_three_mul_transition a
  have htransition :=
    Real.integral_abs_smoothTransitionSecondDerivative_le_eight_closed
  have hscaled := mul_le_mul_of_nonneg_left htransition (Nat.cast_nonneg 3)
  exact Eq.subst (motive := fun value : ℝ => value ≤ 24)
    hidentity.symm
    (le_trans hscaled (le_of_eq (show (3 : ℝ) * 8 = 24 from rfl)))

theorem Real.integral_abs_rightCollarSecondDerivative_eq_three_mul_transition
    (b : ℤ) :
    (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
      |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
      3 * (∫ y in (0 : ℝ)..1,
        |Real.smoothTransitionSecondDerivative y|) := by
  let f : ℝ → ℝ := fun y => |Real.smoothTransitionSecondDerivative y|
  have hnegThreeNe : (-3 : ℝ) ≠ 0 := neg_ne_zero.mpr three_ne_zero
  have hsubstitution := intervalIntegral.integral_comp_mul_add
    (f := f) (a := (b : ℝ)) (b := (b : ℝ) + 1 / 3)
    hnegThreeNe (1 + 3 * (b : ℝ))
  have harguments := intervalIntegral.integral_congr
    (fun x hx => congrArg f (Real.rightCollar_affine_argument_eq b x).symm)
  have hintegrand := intervalIntegral.integral_congr
    (fun x hx => Real.abs_rightCutoffSecondDerivative_eq_nine_mul_transition b x)
  have hcomposed := Eq.trans harguments hsubstitution
  have hendpoints :
      (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) = 1 ∧
      (-3) * ((b : ℝ) + 1 / 3) + (1 + 3 * (b : ℝ)) = 0 :=
    ⟨Real.rightCollar_affine_left_endpoint b,
      Real.rightCollar_affine_right_endpoint b⟩
  have horientation := intervalIntegral.integral_symm f (0 : ℝ) 1
  have hcoefficient : 9 * (-3 : ℝ)⁻¹ * (-1) = 3 := by
    have hnegInv : (-3 : ℝ)⁻¹ = -(1 / 3) := by
      exact inv_neg (3 : ℝ)
    calc
      9 * (-3 : ℝ)⁻¹ * (-1) = 9 * (-(1 / 3)) * (-1) :=
        congrArg (fun value : ℝ => 9 * value * (-1)) hnegInv
      _ = 9 * (1 / 3) := by
        exact (mul_neg 9 (1 / 3)).trans
          (neg_mul_neg_one (9 * (1 / 3)))
      _ = 3 := by
        have hthreeNe : (3 : ℝ) ≠ 0 := three_ne_zero
        exact (mul_div_assoc 9 1 3).trans
          (Eq.trans (congrArg (fun value : ℝ => value / 3) (mul_one 9))
            ((div_eq_iff₀ hthreeNe).2 rfl))
  exact Eq.trans hintegrand
    (Eq.trans (intervalIntegral.integral_const_mul 9)
      (Eq.trans (congrArg (fun value : ℝ => 9 * value) hcomposed)
        (Eq.trans
          (congrArg
            (fun endpoints : ℝ × ℝ =>
              9 * ((-3 : ℝ)⁻¹ • ∫ y in endpoints.1..endpoints.2, f y))
            (Prod.ext hendpoints.1 hendpoints.2))
          (Eq.trans
            (congrArg (fun value : ℝ => 9 * ((-3 : ℝ)⁻¹ * value))
              horientation)
            (Eq.trans
              (mul_assoc 9 (-3 : ℝ)⁻¹
                (-(∫ y in (0 : ℝ)..1, f y))).symm
              (congrArg (fun coefficient : ℝ => coefficient *
                (∫ y in (0 : ℝ)..1, f y)) hcoefficient)))))

theorem Real.integral_abs_rightCollarSecondDerivative_le_twenty_four
    (b : ℤ) :
    (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
      |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) ≤ 24 := by
  have hidentity :=
    Real.integral_abs_rightCollarSecondDerivative_eq_three_mul_transition b
  have htransition :=
    Real.integral_abs_smoothTransitionSecondDerivative_le_eight_closed
  have hscaled := mul_le_mul_of_nonneg_left htransition (Nat.cast_nonneg 3)
  exact Eq.subst (motive := fun value : ℝ => value ≤ 24)
    hidentity.symm
    (le_trans hscaled (le_of_eq (show (3 : ℝ) * 8 = 24 from rfl)))

theorem Real.integral_abs_leftCutoffSecondDerivative_full_le_twenty_four
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤ 24 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let core := (a : ℝ)
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hsplit := intervalIntegral.integral_add_adjacent
    (fun x : ℝ => |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
    left core right
  have hzero :
      (∫ x in core..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) = 0 := by
    exact intervalIntegral.integral_eq_zero_of_eq_zero
      (fun x hx => congrArg abs
        (Real.quantitativeLogarithmicLeftCutoffSecondDerivative_eq_zero_of_core_le
          a hx.1))
  have hidentity :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
      ∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| := by
    unfold left core
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    exact hsplit.trans
      ((congrArg (fun value : ℝ =>
        (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) + value)
        hzero).trans (add_zero _))
  exact le_trans (le_of_eq hidentity)
    (Real.integral_abs_leftCollarSecondDerivative_le_twenty_four a)

theorem Real.integral_abs_rightCutoffSecondDerivative_full_le_twenty_four
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) ≤ 24 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let core := (b : ℝ)
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hsplit := intervalIntegral.integral_add_adjacent
    (fun x : ℝ => |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
    left core right
  have hzero :
      (∫ x in left..core,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) = 0 := by
    exact intervalIntegral.integral_eq_zero_of_eq_zero
      (fun x hx => congrArg abs
        (Real.quantitativeLogarithmicRightCutoffSecondDerivative_eq_zero_of_le_core
          b hx.2))
  have hidentity :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
      ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| := by
    unfold core right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact hsplit.trans
      ((congrArg (fun value : ℝ => value +
        (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|))
        hzero).trans (zero_add _))
  exact le_trans (le_of_eq hidentity)
    (Real.integral_abs_rightCollarSecondDerivative_le_twenty_four b)

theorem Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_forty_eight
    (a b : ℤ)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b ≤ 48 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have hleftRight :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_le_right a b hab
  have hblock :=
    Complex.intervalIntegrable_logarithmicPhaseQuantitativeCutoffCurvatureDensity
      a b left right
  have hcollars : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| +
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left right :=
    ((Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
      .intervalIntegrable left right).add
      ((Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
        .intervalIntegrable left right)
  have hmono := intervalIntegral.integral_mono_on hleftRight hblock hcollars
    (fun x hx =>
      Real.abs_quantitativeLogarithmicBlockCutoffSecondDerivative_le_collars
        a b hab x)
  have hadd := intervalIntegral.integral_add
    ((Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
      .intervalIntegrable left right)
    ((Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
      .intervalIntegrable left right)
  have hleft :=
    Real.integral_abs_leftCutoffSecondDerivative_full_le_twenty_four a b hab
  have hright :=
    Real.integral_abs_rightCutoffSecondDerivative_full_le_twenty_four a b hab
  have hsumBound := add_le_add hleft hright
  have hsum : (24 : ℝ) + 24 = 48 := rfl
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  exact le_trans hmono
    (le_trans (le_of_eq hadd)
      (le_trans hsumBound (le_of_eq hsum)))

end
end LFunctions
end Boundary
