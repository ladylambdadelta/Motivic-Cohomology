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
    _ = (3 * x + -(3 * (a : ℝ))) + 1 :=
      congrArg (fun value : ℝ => value + 1)
        (sub_eq_add_neg (3 * x) (3 * (a : ℝ)))
    _ = 3 * x + (-(3 * (a : ℝ)) + 1) :=
      add_assoc (3 * x) (-(3 * (a : ℝ))) 1
    _ = 3 * x + (1 + -(3 * (a : ℝ))) :=
      congrArg (fun value : ℝ => 3 * x + value)
        (add_comm (-(3 * (a : ℝ))) 1)
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
    _ = (3 * (b : ℝ) + -(3 * x)) + 1 :=
      congrArg (fun value : ℝ => value + 1)
        (sub_eq_add_neg (3 * (b : ℝ)) (3 * x))
    _ = (-(3 * x) + 3 * (b : ℝ)) + 1 :=
      congrArg (fun value : ℝ => value + 1)
        (add_comm (3 * (b : ℝ)) (-(3 * x)))
    _ = -(3 * x) + (3 * (b : ℝ) + 1) :=
      add_assoc (-(3 * x)) (3 * (b : ℝ)) 1
    _ = (-3) * x + (3 * (b : ℝ) + 1) :=
      congrArg (fun value : ℝ => value + (3 * (b : ℝ) + 1))
        (neg_mul 3 x).symm
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
    _ = (3 * (a : ℝ) - 1) + -(3 * (a : ℝ) - 1) :=
      congrArg (fun value : ℝ => (3 * (a : ℝ) - 1) + value)
        (neg_sub (3 * (a : ℝ)) 1).symm
    _ = 0 := add_neg_cancel (3 * (a : ℝ) - 1)

theorem Real.leftCollar_affine_right_endpoint
    (a : ℤ) :
    3 * (a : ℝ) + (1 - 3 * (a : ℝ)) = 1 := by
  calc
    3 * (a : ℝ) + (1 - 3 * (a : ℝ)) =
        3 * (a : ℝ) + (1 + -(3 * (a : ℝ))) :=
      congrArg (fun value : ℝ => 3 * (a : ℝ) + value)
        (sub_eq_add_neg 1 (3 * (a : ℝ)))
    _ = (3 * (a : ℝ) + 1) + -(3 * (a : ℝ)) :=
      (add_assoc (3 * (a : ℝ)) 1 (-(3 * (a : ℝ)))).symm
    _ = (1 + 3 * (a : ℝ)) + -(3 * (a : ℝ)) :=
      congrArg (fun value : ℝ => value + -(3 * (a : ℝ)))
        (add_comm (3 * (a : ℝ)) 1)
    _ = 1 + (3 * (a : ℝ) + -(3 * (a : ℝ))) :=
      add_assoc 1 (3 * (a : ℝ)) (-(3 * (a : ℝ)))
    _ = 1 + 0 :=
      congrArg (fun value : ℝ => 1 + value)
        (add_neg_cancel (3 * (a : ℝ)))
    _ = 1 := add_zero 1

theorem Real.rightCollar_affine_left_endpoint
    (b : ℤ) :
    (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) = 1 := by
  calc
    (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) =
        -(3 * (b : ℝ)) + (1 + 3 * (b : ℝ)) :=
      congrArg (fun value : ℝ => value + (1 + 3 * (b : ℝ)))
        (neg_mul 3 (b : ℝ))
    _ = (-(3 * (b : ℝ)) + 1) + 3 * (b : ℝ) :=
      (add_assoc (-(3 * (b : ℝ))) 1 (3 * (b : ℝ))).symm
    _ = (1 + -(3 * (b : ℝ))) + 3 * (b : ℝ) :=
      congrArg (fun value : ℝ => value + 3 * (b : ℝ))
        (add_comm (-(3 * (b : ℝ))) 1)
    _ = 1 + (-(3 * (b : ℝ)) + 3 * (b : ℝ)) :=
      add_assoc 1 (-(3 * (b : ℝ))) (3 * (b : ℝ))
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
      have hnegativeThird : (-3 : ℝ) * (1 / 3) = -1 :=
        Eq.trans (neg_mul 3 (1 / 3))
          (congrArg Neg.neg (mul_one_div_cancel hthreeNe))
      exact congrArg
        (fun value : ℝ => ((-3) * (b : ℝ) + value) +
          (1 + 3 * (b : ℝ)))
        hnegativeThird
    _ = 0 := by
      have hfirst : (-3) * (b : ℝ) + (-1) =
          -(1 + 3 * (b : ℝ)) := by
        exact Eq.trans
          (congrArg (fun value : ℝ => value + (-1))
            (neg_mul 3 (b : ℝ)))
          (neg_add_rev 1 (3 * (b : ℝ))).symm
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
  have harguments :
      (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        f (3 * (x - (a : ℝ)) + 1)) =
      ∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        f (3 * x + (1 - 3 * (a : ℝ))) :=
    intervalIntegral.integral_congr
      (a := (a : ℝ) - 1 / 3) (b := (a : ℝ)) (μ := volume)
    (fun x hx => congrArg f (Real.leftCollar_affine_argument_eq a x))
  have hendpointPair :
      (3 * ((a : ℝ) - 1 / 3) + (1 - 3 * (a : ℝ)),
          3 * (a : ℝ) + (1 - 3 * (a : ℝ))) =
        ((0 : ℝ), (1 : ℝ)) := by
    exact congrArg₂ (fun x y : ℝ => (x, y))
      (Real.leftCollar_affine_left_endpoint a)
      (Real.leftCollar_affine_right_endpoint a)
  have hendpoints := congrArg
    (fun leftRight : ℝ × ℝ =>
      (3 : ℝ)⁻¹ • ∫ y in leftRight.1..leftRight.2, f y)
    hendpointPair
  have hscaled := congrArg (fun value : ℝ => 9 * value)
    (Eq.trans harguments hsubstitution)
  have hintegrand :
      (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
      ∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        9 * f (3 * (x - (a : ℝ)) + 1) :=
    intervalIntegral.integral_congr
      (a := (a : ℝ) - 1 / 3) (b := (a : ℝ)) (μ := volume)
    (fun x hx => Real.abs_leftCutoffSecondDerivative_eq_nine_mul_transition a x)
  have hcoefficient : 9 * (3 : ℝ)⁻¹ = 3 := by
    have hthreeThree : (3 : ℝ) * 3 = 9 :=
      Real.transitionSecondDerivative_natCast_mul 3 3 9 rfl
    calc
      9 * (3 : ℝ)⁻¹ = (3 * 3) * (3 : ℝ)⁻¹ := by
        exact congrArg (fun value : ℝ => value * (3 : ℝ)⁻¹)
          hthreeThree.symm
      _ = 3 * (3 * (3 : ℝ)⁻¹) :=
        mul_assoc 3 3 (3 : ℝ)⁻¹
      _ = 3 * 1 := by
        exact congrArg (fun value : ℝ => 3 * value)
          (mul_inv_cancel₀ hthreeNe)
      _ = 3 :=
        mul_one 3
  have hconstant := intervalIntegral.integral_const_mul
    (f := fun x : ℝ => f (3 * (x - (a : ℝ)) + 1))
    (a := (a : ℝ) - 1 / 3) (b := (a : ℝ)) (μ := volume) 9
  have hendpointScaled :=
    congrArg (fun value : ℝ => 9 * value) hendpoints
  have hreassociated :
      9 * ((3 : ℝ)⁻¹ * (∫ y in (0 : ℝ)..1, f y)) =
        (9 * (3 : ℝ)⁻¹) * (∫ y in (0 : ℝ)..1, f y) :=
    (mul_assoc 9 (3 : ℝ)⁻¹
      (∫ y in (0 : ℝ)..1, f y)).symm
  have hcoefficientScaled :=
    congrArg (fun coefficient : ℝ => coefficient *
      (∫ y in (0 : ℝ)..1, f y)) hcoefficient
  exact hintegrand.trans
    (hconstant.trans
      (hscaled.trans
        (hendpointScaled.trans
          (hreassociated.trans hcoefficientScaled))))

theorem Real.integral_abs_leftCollarSecondDerivative_le_twenty_four
    (a : ℤ) :
    (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤ 24 := by
  have hidentity :=
    Real.integral_abs_leftCollarSecondDerivative_eq_three_mul_transition a
  have htransition :=
    Real.integral_abs_smoothTransitionSecondDerivative_le_eight_closed
  have hscaled := mul_le_mul_of_nonneg_left htransition (Nat.cast_nonneg 3)
  have hproduct : (3 : ℝ) * 8 = 24 :=
    Real.transitionSecondDerivative_natCast_mul 3 8 24 rfl
  exact Eq.subst (motive := fun value : ℝ => value ≤ 24)
    hidentity.symm
    (le_trans hscaled (le_of_eq hproduct))

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
  have harguments :
      (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        f (3 * ((b : ℝ) - x) + 1)) =
      ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        f ((-3) * x + (1 + 3 * (b : ℝ))) :=
    intervalIntegral.integral_congr
      (a := (b : ℝ)) (b := (b : ℝ) + 1 / 3) (μ := volume)
    (fun x hx => congrArg f (Real.rightCollar_affine_argument_eq b x))
  have hintegrand :
      (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
      ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        9 * f (3 * ((b : ℝ) - x) + 1) :=
    intervalIntegral.integral_congr
      (a := (b : ℝ)) (b := (b : ℝ) + 1 / 3) (μ := volume)
    (fun x hx => Real.abs_rightCutoffSecondDerivative_eq_nine_mul_transition b x)
  have hcomposed := Eq.trans harguments hsubstitution
  have hendpoints :
      (-3) * (b : ℝ) + (1 + 3 * (b : ℝ)) = 1 ∧
      (-3) * ((b : ℝ) + 1 / 3) + (1 + 3 * (b : ℝ)) = 0 :=
    ⟨Real.rightCollar_affine_left_endpoint b,
      Real.rightCollar_affine_right_endpoint b⟩
  have hendpointPair :
      ((-3) * (b : ℝ) + (1 + 3 * (b : ℝ)),
          (-3) * ((b : ℝ) + 1 / 3) + (1 + 3 * (b : ℝ))) =
        ((1 : ℝ), (0 : ℝ)) :=
    congrArg₂ (fun x y : ℝ => (x, y)) hendpoints.1 hendpoints.2
  have horientation := intervalIntegral.integral_symm
    (f := f) (μ := volume) (0 : ℝ) 1
  have hcoefficient : 9 * (-3 : ℝ)⁻¹ * (-1) = 3 := by
    have hnegInv : (-3 : ℝ)⁻¹ = -((3 : ℝ)⁻¹) :=
      inv_neg
    have hpositive : 9 * (3 : ℝ)⁻¹ = 3 := by
      have hthreeThree : (3 : ℝ) * 3 = 9 :=
        Real.transitionSecondDerivative_natCast_mul 3 3 9 rfl
      calc
        9 * (3 : ℝ)⁻¹ = (3 * 3) * (3 : ℝ)⁻¹ := by
          exact congrArg (fun value : ℝ => value * (3 : ℝ)⁻¹)
            hthreeThree.symm
        _ = 3 * (3 * (3 : ℝ)⁻¹) :=
          mul_assoc 3 3 (3 : ℝ)⁻¹
        _ = 3 * 1 := by
          exact congrArg (fun value : ℝ => 3 * value)
            (mul_inv_cancel₀ three_ne_zero)
        _ = 3 :=
          mul_one 3
    calc
      9 * (-3 : ℝ)⁻¹ * (-1) = 9 * (-((3 : ℝ)⁻¹)) * (-1) :=
        congrArg (fun value : ℝ => 9 * value * (-1)) hnegInv
      _ = -(9 * (3 : ℝ)⁻¹) * (-1) := by
        exact congrArg (fun value : ℝ => value * (-1))
          (mul_neg 9 (3 : ℝ)⁻¹)
      _ = 9 * (3 : ℝ)⁻¹ := by
        exact Eq.trans
          (neg_mul_neg (9 * (3 : ℝ)⁻¹) 1)
          (mul_one (9 * (3 : ℝ)⁻¹))
      _ = 3 := hpositive
  have hconstant := intervalIntegral.integral_const_mul
    (f := fun x : ℝ => f (3 * ((b : ℝ) - x) + 1))
    (a := (b : ℝ)) (b := (b : ℝ) + 1 / 3) (μ := volume) 9
  have hscaled := congrArg (fun value : ℝ => 9 * value) hcomposed
  have hendpointScaled :=
    congrArg
      (fun endpoints : ℝ × ℝ =>
        9 * ((-3 : ℝ)⁻¹ • ∫ y in endpoints.1..endpoints.2, f y))
      hendpointPair
  have horientationScaled :=
    congrArg (fun value : ℝ => 9 * ((-3 : ℝ)⁻¹ * value))
      horientation
  have hfirstAssociation :
      9 * ((-3 : ℝ)⁻¹ * (-(∫ y in (0 : ℝ)..1, f y))) =
        (9 * (-3 : ℝ)⁻¹) * (-(∫ y in (0 : ℝ)..1, f y)) :=
    (mul_assoc 9 (-3 : ℝ)⁻¹
      (-(∫ y in (0 : ℝ)..1, f y))).symm
  have hnegativeAsProduct :=
    congrArg
      (fun value : ℝ => (9 * (-3 : ℝ)⁻¹) * value)
      (neg_eq_neg_one_mul (∫ y in (0 : ℝ)..1, f y))
  have hsecondAssociation :
      (9 * (-3 : ℝ)⁻¹) *
          ((-1) * (∫ y in (0 : ℝ)..1, f y)) =
        ((9 * (-3 : ℝ)⁻¹) * (-1)) *
          (∫ y in (0 : ℝ)..1, f y) :=
    (mul_assoc (9 * (-3 : ℝ)⁻¹) (-1)
      (∫ y in (0 : ℝ)..1, f y)).symm
  have hcoefficientScaled :=
    congrArg (fun coefficient : ℝ => coefficient *
      (∫ y in (0 : ℝ)..1, f y)) hcoefficient
  exact hintegrand.trans
    (hconstant.trans
      (hscaled.trans
        (hendpointScaled.trans
          (horientationScaled.trans
            (hfirstAssociation.trans
              (hnegativeAsProduct.trans
                (hsecondAssociation.trans hcoefficientScaled)))))))

theorem Real.integral_abs_rightCollarSecondDerivative_le_twenty_four
    (b : ℤ) :
    (∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
      |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) ≤ 24 := by
  have hidentity :=
    Real.integral_abs_rightCollarSecondDerivative_eq_three_mul_transition b
  have htransition :=
    Real.integral_abs_smoothTransitionSecondDerivative_le_eight_closed
  have hscaled := mul_le_mul_of_nonneg_left htransition (Nat.cast_nonneg 3)
  have hproduct : (3 : ℝ) * 8 = 24 :=
    Real.transitionSecondDerivative_natCast_mul 3 8 24 rfl
  exact Eq.subst (motive := fun value : ℝ => value ≤ 24)
    hidentity.symm
    (le_trans hscaled (le_of_eq hproduct))

theorem Real.integral_abs_leftCutoffSecondDerivative_full_le_twenty_four
    (a b : ℤ)
    (hab : a ≤ b) :
    (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..
        Complex.logarithmicPhaseQuantitativeSupportRight b,
      |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) ≤ 24 := by
  let left := Complex.logarithmicPhaseQuantitativeSupportLeft a
  let core := (a : ℝ)
  let right := Complex.logarithmicPhaseQuantitativeSupportRight b
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 :=
    le_of_lt Real.one_div_three_pos
  have hcoreRight : core ≤ right := by
    unfold core right
    unfold Complex.logarithmicPhaseQuantitativeSupportRight
    exact le_trans habReal (le_add_of_nonneg_right hthirdNonneg)
  have hcontinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) :=
    (Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume left core :=
    hcontinuous.intervalIntegrable left core
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume core right :=
    hcontinuous.intervalIntegrable core right
  have hsplit :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
        (∫ x in left..core,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) +
        ∫ x in core..right,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| :=
    (intervalIntegral.integral_add_adjacent_intervals
      hleftIntegrable hrightIntegrable).symm
  have hzero :
      (∫ x in core..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) = 0 := by
    have hzeroIntegral :
        (∫ x in core..right,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
        ∫ x in core..right, (0 : ℝ) :=
      intervalIntegral.integral_congr
        (a := core) (b := right) (μ := volume)
        (fun x hx => by
          have hxIcc : x ∈ Set.Icc core right :=
            (Set.uIcc_of_le hcoreRight).symm ▸ hx
          exact Eq.trans
              (congrArg abs
                (Real.quantitativeLogarithmicLeftCutoffSecondDerivative_eq_zero_of_core_le
                  a hxIcc.1))
              (abs_zero : |(0 : ℝ)| = 0))
    exact Eq.trans hzeroIntegral intervalIntegral.integral_zero
  have hidentity :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
      ∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| := by
    have hsplitConcrete :
        (∫ x in Complex.logarithmicPhaseQuantitativeSupportLeft a..right,
          |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) =
          (∫ x in ((a : ℝ) - 1 / 3)..(a : ℝ),
            |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) +
          ∫ x in (a : ℝ)..right,
            |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| :=
      hsplit
    exact hsplitConcrete.trans
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
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  have hthirdNonneg : (0 : ℝ) ≤ 1 / 3 :=
    le_of_lt Real.one_div_three_pos
  have hleftCore : left ≤ core := by
    unfold left core
    unfold Complex.logarithmicPhaseQuantitativeSupportLeft
    have haLeft : (a : ℝ) - 1 / 3 ≤ (a : ℝ) :=
      sub_le_self (a : ℝ) hthirdNonneg
    exact le_trans haLeft habReal
  have hcontinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) :=
    (Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left core :=
    hcontinuous.intervalIntegrable left core
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume core right :=
    hcontinuous.intervalIntegrable core right
  have hsplit :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
        (∫ x in left..core,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) +
        ∫ x in core..right,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| :=
    (intervalIntegral.integral_add_adjacent_intervals
      hleftIntegrable hrightIntegrable).symm
  have hzero :
      (∫ x in left..core,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) = 0 := by
    have hzeroIntegral :
        (∫ x in left..core,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
        ∫ x in left..core, (0 : ℝ) :=
      intervalIntegral.integral_congr
        (a := left) (b := core) (μ := volume)
        (fun x hx => by
          have hxIcc : x ∈ Set.Icc left core :=
            (Set.uIcc_of_le hleftCore).symm ▸ hx
          exact Eq.trans
              (congrArg abs
                (Real.quantitativeLogarithmicRightCutoffSecondDerivative_eq_zero_of_le_core
                  b hxIcc.2))
              (abs_zero : |(0 : ℝ)| = 0))
    exact Eq.trans hzeroIntegral intervalIntegral.integral_zero
  have hidentity :
      (∫ x in left..right,
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
      ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| := by
    have hsplitConcrete :
        (∫ x in left..Complex.logarithmicPhaseQuantitativeSupportRight b,
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) =
          (∫ x in left..(b : ℝ),
            |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) +
          ∫ x in (b : ℝ)..((b : ℝ) + 1 / 3),
            |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x| :=
      hsplit
    exact hsplitConcrete.trans
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
  have hleftContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|) :=
    (Real.continuous_quantitativeLogarithmicLeftCutoffSecondDerivative a).abs
  have hrightContinuous : Continuous
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|) :=
    (Real.continuous_quantitativeLogarithmicRightCutoffSecondDerivative b).abs
  have hleftIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x|)
      volume left right :=
    hleftContinuous.intervalIntegrable left right
  have hrightIntegrable : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left right :=
    hrightContinuous.intervalIntegrable left right
  have hcollars : IntervalIntegrable
      (fun x : ℝ =>
        |Real.quantitativeLogarithmicLeftCutoffSecondDerivative a x| +
          |Real.quantitativeLogarithmicRightCutoffSecondDerivative b x|)
      volume left right :=
    hleftIntegrable.add hrightIntegrable
  have hmono := intervalIntegral.integral_mono_on hleftRight hblock hcollars
    (fun x hx =>
      Real.abs_quantitativeLogarithmicBlockCutoffSecondDerivative_le_collars
        a b hab x)
  have hadd := intervalIntegral.integral_add
    hleftIntegrable hrightIntegrable
  have hleft :=
    Real.integral_abs_leftCutoffSecondDerivative_full_le_twenty_four a b hab
  have hright :=
    Real.integral_abs_rightCutoffSecondDerivative_full_le_twenty_four a b hab
  have hsumBound := add_le_add hleft hright
  have hsum : (24 : ℝ) + 24 = 48 :=
    Real.transitionSecondDerivative_natCast_add 24 24 48 rfl
  unfold Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass
  exact le_trans hmono
    (le_trans (le_of_eq hadd)
      (le_trans hsumBound (le_of_eq hsum)))

end
end LFunctions
end Boundary
