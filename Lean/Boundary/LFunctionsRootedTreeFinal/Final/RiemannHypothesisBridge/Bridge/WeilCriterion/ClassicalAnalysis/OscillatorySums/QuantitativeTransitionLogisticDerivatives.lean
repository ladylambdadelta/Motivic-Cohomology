import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionCoordinateRatio

/-!
# Logistic derivative coordinates for the flat transition

On `0<x<1`, the transition is the decreasing logistic of the reciprocal gap
`d=x⁻¹-(1-x)⁻¹`.  This owner differentiates the gap and logistic factor in a
form adapted to the scalar curvature comparison.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.decreasingLogistic (z : ℝ) : ℝ :=
  (1 + Real.exp z)⁻¹

def Real.decreasingLogisticDerivative (z : ℝ) : ℝ :=
  -(Real.exp z * (1 + Real.exp z)⁻¹ ^ 2)

def Real.decreasingLogisticSecondDerivative (z : ℝ) : ℝ :=
  Real.exp z * (Real.exp z - 1) * (1 + Real.exp z)⁻¹ ^ 3

def Real.transitionGapDerivative (x : ℝ) : ℝ :=
  -(Real.transitionReciprocalEnergy x)

def Real.transitionGapSecondDerivative (x : ℝ) : ℝ :=
  2 * Real.transitionReciprocalGap x *
    Real.transitionReciprocalCubicSum x

theorem Real.transitionReciprocalGap_eq
    (x : ℝ) :
    Real.transitionReciprocalGap x = x⁻¹ - (1 - x)⁻¹ := by
  rfl

theorem Real.hasDerivAt_transitionLeftReciprocal
    {x : ℝ}
    (hx : x ≠ 0) :
    HasDerivAt Real.transitionLeftReciprocal (-(x⁻¹ ^ 2)) x := by
  unfold Real.transitionLeftReciprocal
  exact (hasDerivAt_id x).inv hx

theorem Real.hasDerivAt_transitionRightReciprocal
    {x : ℝ}
    (hx : 1 - x ≠ 0) :
    HasDerivAt Real.transitionRightReciprocal ((1 - x)⁻¹ ^ 2) x := by
  unfold Real.transitionRightReciprocal
  have hinner := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hinverse := hinner.inv hx
  have hnormalize : -1 * -(1 - x)⁻¹ ^ 2 = (1 - x)⁻¹ ^ 2 := by
    exact neg_mul_neg_one ((1 - x)⁻¹ ^ 2)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => (1 - y)⁻¹) value x)
    hnormalize
    hinverse

theorem Real.hasDerivAt_transitionReciprocalGap
    {x : ℝ}
    (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    HasDerivAt Real.transitionReciprocalGap
      (Real.transitionGapDerivative x) x := by
  unfold Real.transitionReciprocalGap
  unfold Real.transitionGapDerivative
  unfold Real.transitionReciprocalEnergy
  have hleft := Real.hasDerivAt_transitionLeftReciprocal hx0
  have hright := Real.hasDerivAt_transitionRightReciprocal hx1
  have hdifference := hleft.sub hright
  have hnormalize :
      -(x⁻¹ ^ 2) - (1 - x)⁻¹ ^ 2 =
        -(x⁻¹ ^ 2 + (1 - x)⁻¹ ^ 2) := by
    exact (neg_sub _ _).symm.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        rfl (neg_neg ((1 - x)⁻¹ ^ 2))).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => y⁻¹ - (1 - y)⁻¹) value x)
    hnormalize
    hdifference

theorem Real.hasDerivAt_transitionReciprocalEnergy
    {x : ℝ}
    (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    HasDerivAt Real.transitionReciprocalEnergy
      (-2 * x⁻¹ ^ 3 + 2 * (1 - x)⁻¹ ^ 3) x := by
  unfold Real.transitionReciprocalEnergy
  have hleft := (Real.hasDerivAt_transitionLeftReciprocal hx0).pow 2
  have hright := (Real.hasDerivAt_transitionRightReciprocal hx1).pow 2
  have hsum := hleft.add hright
  have hnormalize :
      2 * x⁻¹ ^ (2 - 1) * (-(x⁻¹ ^ 2)) +
          2 * (1 - x)⁻¹ ^ (2 - 1) * ((1 - x)⁻¹ ^ 2) =
        -2 * x⁻¹ ^ 3 + 2 * (1 - x)⁻¹ ^ 3 := by
    have hpowLeft : x⁻¹ ^ (2 - 1) = x⁻¹ := pow_one x⁻¹
    have hpowRight : (1 - x)⁻¹ ^ (2 - 1) = (1 - x)⁻¹ :=
      pow_one (1 - x)⁻¹
    exact Eq.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg (fun value : ℝ => 2 * value * (-(x⁻¹ ^ 2))) hpowLeft)
        (congrArg (fun value : ℝ =>
          2 * value * ((1 - x)⁻¹ ^ 2)) hpowRight))
      (congrArg₂ (fun first second : ℝ => first + second)
        ((mul_neg (2 * x⁻¹) (x⁻¹ ^ 2)).trans
          (congrArg Neg.neg
            ((mul_assoc 2 x⁻¹ (x⁻¹ ^ 2)).trans
              (congrArg (fun value : ℝ => 2 * value)
                (pow_succ x⁻¹ 2).symm))))
        ((mul_assoc 2 (1 - x)⁻¹ ((1 - x)⁻¹ ^ 2)).trans
          (congrArg (fun value : ℝ => 2 * value)
            (pow_succ (1 - x)⁻¹ 2).symm)))
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => y⁻¹ ^ 2 + (1 - y)⁻¹ ^ 2) value x)
    hnormalize
    hsum

theorem Real.transitionGapSecondDerivative_eq_cubic_difference
    (x : ℝ) :
    Real.transitionGapSecondDerivative x =
      2 * x⁻¹ ^ 3 - 2 * (1 - x)⁻¹ ^ 3 := by
  unfold Real.transitionGapSecondDerivative
  unfold Real.transitionReciprocalGap
  unfold Real.transitionReciprocalCubicSum
  let p := x⁻¹
  let q := (1 - x)⁻¹
  change 2 * (p - q) * (p ^ 2 + p * q + q ^ 2) =
    2 * p ^ 3 - 2 * q ^ 3
  have hcubes :
      (p - q) * (p ^ 2 + p * q + q ^ 2) = p ^ 3 - q ^ 3 := by
    calc
      (p - q) * (p ^ 2 + p * q + q ^ 2) =
          p * (p ^ 2 + p * q + q ^ 2) -
            q * (p ^ 2 + p * q + q ^ 2) :=
        sub_mul p q _
      _ = (p * p ^ 2 + p * (p * q) + p * q ^ 2) -
          (q * p ^ 2 + q * (p * q) + q * q ^ 2) := by
        exact congrArg₂ (fun first second : ℝ => first - second)
          ((mul_add p (p ^ 2 + p * q) (q ^ 2)).trans
            (congrArg (fun value : ℝ => value + p * q ^ 2)
              (mul_add p (p ^ 2) (p * q))))
          ((mul_add q (p ^ 2 + p * q) (q ^ 2)).trans
            (congrArg (fun value : ℝ => value + q * q ^ 2)
              (mul_add q (p ^ 2) (p * q))))
      _ = p ^ 3 - q ^ 3 := by
        have hpCube : p * p ^ 2 = p ^ 3 := (pow_succ p 2).symm
        have hqCube : q * q ^ 2 = q ^ 3 := (pow_succ q 2).symm
        have hcrossOne : p * (p * q) = q * p ^ 2 := by
          exact (mul_assoc p p q).symm.trans
            (congrArg (fun value : ℝ => value * q) (pow_two p).symm).trans
            (mul_comm (p ^ 2) q)
        have hcrossTwo : p * q ^ 2 = q * (p * q) := by
          exact (mul_assoc q p q).symm.trans
            (congrArg (fun value : ℝ => value * q) (mul_comm q p)).symm.trans
            (mul_assoc p q q).trans
            (congrArg (fun value : ℝ => p * value) (pow_two q).symm).symm
        exact Eq.trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (congrArg₂ (fun first second : ℝ => first + second)
              (congrArg₂ (fun first second : ℝ => first + second)
                hpCube hcrossOne) hcrossTwo)
            (congrArg₂ (fun first second : ℝ => first + second)
              (congrArg₂ (fun first second : ℝ => first + second)
                rfl rfl) hqCube))
          (add_sub_add_left_eq_sub (p ^ 3) (q ^ 3)
            (q * p ^ 2 + q * (p * q)))
  exact Eq.trans
    (congrArg (fun value : ℝ => 2 * value) hcubes)
    (mul_sub 2 (p ^ 3) (q ^ 3))

theorem Real.hasDerivAt_transitionGapDerivative
    {x : ℝ}
    (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    HasDerivAt Real.transitionGapDerivative
      (Real.transitionGapSecondDerivative x) x := by
  unfold Real.transitionGapDerivative
  have henergy := Real.hasDerivAt_transitionReciprocalEnergy hx0 hx1
  have hnegative := henergy.neg
  have hnormalize :
      -(-2 * x⁻¹ ^ 3 + 2 * (1 - x)⁻¹ ^ 3) =
        Real.transitionGapSecondDerivative x := by
    exact Eq.trans
      (neg_add _ _)
      (Eq.trans
        (congrArg₂ (fun first second : ℝ => first + second)
          (neg_neg (2 * x⁻¹ ^ 3)) (neg_mul 2 ((1 - x)⁻¹ ^ 3)))
        (Eq.trans
          (sub_eq_add_neg (2 * x⁻¹ ^ 3)
            (2 * (1 - x)⁻¹ ^ 3)).symm
          (Real.transitionGapSecondDerivative_eq_cubic_difference x).symm))
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => -Real.transitionReciprocalEnergy y)
        value x)
    hnormalize
    hnegative

theorem Real.hasDerivAt_decreasingLogistic
    (z : ℝ) :
    HasDerivAt Real.decreasingLogistic
      (Real.decreasingLogisticDerivative z) z := by
  unfold Real.decreasingLogistic
  unfold Real.decreasingLogisticDerivative
  have hinner := (hasDerivAt_const z 1).add (Real.hasDerivAt_exp z)
  have hne : 1 + Real.exp z ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos z))
  have hinverse := hinner.inv hne
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹) value z)
    (mul_comm (-(1 + Real.exp z)⁻¹ ^ 2) (Real.exp z))
    hinverse

theorem Real.hasDerivAt_decreasingLogisticDerivative
    (z : ℝ) :
    HasDerivAt Real.decreasingLogisticDerivative
      (Real.decreasingLogisticSecondDerivative z) z := by
  let e := Real.exp z
  let u := 1 + e
  have he : HasDerivAt Real.exp e z := Real.hasDerivAt_exp z
  have hu : HasDerivAt (fun y : ℝ => 1 + Real.exp y) e z :=
    (hasDerivAt_const z 1).add he
  have huNe : u ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos z))
  have huInv : HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹)
      (-(u⁻¹ ^ 2) * e) z :=
    hu.inv huNe
  have huInvSq := huInv.pow 2
  have hproduct := he.mul huInvSq
  have hnegative := hproduct.neg
  unfold Real.decreasingLogisticDerivative
  unfold Real.decreasingLogisticSecondDerivative
  change HasDerivAt
    (fun y : ℝ => -(Real.exp y * (1 + Real.exp y)⁻¹ ^ 2))
    (e * (e - 1) * u⁻¹ ^ 3) z
  have hraw := hnegative
  have hnormalize :
      -(e * u⁻¹ ^ 2 +
          e * (2 * u⁻¹ ^ (2 - 1) * (-(u⁻¹ ^ 2) * e))) =
        e * (e - 1) * u⁻¹ ^ 3 := by
    have hpowOne : u⁻¹ ^ (2 - 1) = u⁻¹ := pow_one u⁻¹
    have hpowThree : u⁻¹ * u⁻¹ ^ 2 = u⁻¹ ^ 3 :=
      (pow_succ u⁻¹ 2).symm
    have huIdentity : u = 1 + e := rfl
    calc
      -(e * u⁻¹ ^ 2 +
          e * (2 * u⁻¹ ^ (2 - 1) * (-(u⁻¹ ^ 2) * e))) =
        -(e * u⁻¹ ^ 2 +
          e * (2 * u⁻¹ * (-(u⁻¹ ^ 2) * e))) :=
        congrArg Neg.neg
          (congrArg (fun value : ℝ => e * u⁻¹ ^ 2 +
            e * (2 * value * (-(u⁻¹ ^ 2) * e))) hpowOne)
      _ = -(e * u⁻¹ ^ 2 - 2 * e ^ 2 * u⁻¹ ^ 3) := by
        congr 1
        have hsecond :
            e * (2 * u⁻¹ * (-(u⁻¹ ^ 2) * e)) =
              -(2 * e ^ 2 * u⁻¹ ^ 3) := by
          calc
            e * (2 * u⁻¹ * (-(u⁻¹ ^ 2) * e)) =
                -(e * (2 * u⁻¹ * (u⁻¹ ^ 2 * e))) := by
              exact congrArg (fun value : ℝ => e * value)
                ((congrArg (fun value : ℝ => 2 * u⁻¹ * value)
                  (neg_mul (u⁻¹ ^ 2) e)).trans
                  (mul_neg (2 * u⁻¹) (u⁻¹ ^ 2 * e))).trans
                (mul_neg e (2 * u⁻¹ * (u⁻¹ ^ 2 * e))).symm
            _ = -(2 * e ^ 2 * u⁻¹ ^ 3) := by
              congr 1
              exact
                (mul_assoc e (2 * u⁻¹) (u⁻¹ ^ 2 * e)).trans
                  ((congrArg (fun value : ℝ => value * (u⁻¹ ^ 2 * e))
                    ((mul_assoc e 2 u⁻¹).trans
                      (congrArg (fun value : ℝ => value * u⁻¹)
                        (mul_comm e 2)))).trans
                    (mul_assoc (2 * e * u⁻¹) (u⁻¹ ^ 2) e)).trans
                  (congrArg (fun value : ℝ => 2 * e * value * e)
                    hpowThree).trans
                  ((mul_assoc (2 * e) (u⁻¹ ^ 3) e).trans
                    (congrArg (fun value : ℝ => 2 * value)
                      ((mul_assoc e (u⁻¹ ^ 3) e).trans
                        (congrArg (fun value : ℝ => value * e)
                          (mul_comm e (u⁻¹ ^ 3))).trans
                        (mul_assoc (u⁻¹ ^ 3) e e).symm)).trans
                    (mul_assoc 2 (u⁻¹ ^ 3) (e * e)).trans
                    (congrArg (fun value : ℝ => 2 * u⁻¹ ^ 3 * value)
                      (pow_two e).symm).trans
                    (mul_comm (2 * u⁻¹ ^ 3) (e ^ 2)).trans
                    (mul_assoc 2 (e ^ 2) (u⁻¹ ^ 3)))
        exact congrArg (fun value : ℝ => e * u⁻¹ ^ 2 + value)
          ((sub_eq_add_neg (2 * e ^ 2 * u⁻¹ ^ 3) 0).symm.trans
            hsecond)
      _ = -e * u⁻¹ ^ 2 + 2 * e ^ 2 * u⁻¹ ^ 3 :=
        neg_sub _ _
      _ = e * u⁻¹ ^ 3 * (-u + 2 * e) := by
        have hinverseCollapse : u⁻¹ ^ 3 * u = u⁻¹ ^ 2 := by
          have huInvMul : u⁻¹ * u = 1 := inv_mul_cancel₀ huNe
          calc
            u⁻¹ ^ 3 * u = (u⁻¹ ^ 2 * u⁻¹) * u := by
              exact congrArg (fun value : ℝ => value * u) (pow_succ u⁻¹ 2)
            _ = u⁻¹ ^ 2 * (u⁻¹ * u) :=
              mul_assoc (u⁻¹ ^ 2) u⁻¹ u
            _ = u⁻¹ ^ 2 * 1 :=
              congrArg (fun value : ℝ => u⁻¹ ^ 2 * value) huInvMul
            _ = u⁻¹ ^ 2 := mul_one _
        calc
          -e * u⁻¹ ^ 2 + 2 * e ^ 2 * u⁻¹ ^ 3 =
              -(e * u⁻¹ ^ 3 * u) +
                e * u⁻¹ ^ 3 * (2 * e) := by
            exact congrArg₂ (fun first second : ℝ => first + second)
              (congrArg Neg.neg
                (congrArg (fun value : ℝ => e * value)
                  hinverseCollapse.symm))
              ((mul_assoc (2 * e ^ 2) (u⁻¹ ^ 3) 1).trans
                (mul_comm (2 * e ^ 2) (u⁻¹ ^ 3))).trans
                (mul_assoc (u⁻¹ ^ 3) (2 * e) e).symm.trans
                (mul_assoc e (u⁻¹ ^ 3) (2 * e))
          _ = e * u⁻¹ ^ 3 * (-u + 2 * e) := by
            exact (mul_add (e * u⁻¹ ^ 3) (-u) (2 * e)).symm.trans
              (congrArg₂ (fun first second : ℝ => first + second)
                (mul_neg (e * u⁻¹ ^ 3) u)
                rfl)
      _ = e * (e - 1) * u⁻¹ ^ 3 := by
        have hbracket : -u + 2 * e = e - 1 := by
          unfold u
          calc
            -(1 + e) + 2 * e = (-1 + -e) + (e + e) := by
              exact congrArg₂ (fun first second : ℝ => first + second)
                (neg_add_rev 1 e)
                (two_mul e)
            _ = e - 1 := by
              exact (add_assoc (-1) (-e) (e + e)).trans
                (congrArg (fun value : ℝ => -1 + value)
                  ((add_assoc (-e) e e).symm.trans
                    (congrArg (fun value : ℝ => value + e)
                      (neg_add_cancel e)).trans
                    (zero_add e))).trans
                (add_comm (-1) e).trans
                (sub_eq_add_neg e 1).symm
        exact Eq.trans
          (congrArg (fun value : ℝ => e * u⁻¹ ^ 3 * value) hbracket)
          ((mul_assoc e (u⁻¹ ^ 3) (e - 1)).trans
            (congrArg (fun value : ℝ => e * value)
              (mul_comm (u⁻¹ ^ 3) (e - 1))).trans
            (mul_assoc e (e - 1) (u⁻¹ ^ 3)).symm)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => -(Real.exp y * (1 + Real.exp y)⁻¹ ^ 2))
        value z)
    hnormalize
    hraw

def Real.transitionLogisticFirstDerivative (x : ℝ) : ℝ :=
  Real.decreasingLogisticDerivative
      (Real.transitionReciprocalGap x) *
    Real.transitionGapDerivative x

def Real.transitionLogisticSecondDerivative (x : ℝ) : ℝ :=
  Real.decreasingLogisticSecondDerivative
      (Real.transitionReciprocalGap x) *
      Real.transitionGapDerivative x ^ 2 +
    Real.decreasingLogisticDerivative
      (Real.transitionReciprocalGap x) *
      Real.transitionGapSecondDerivative x

theorem Real.hasDerivAt_transitionLogisticComposite
    {x : ℝ}
    (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        Real.decreasingLogistic (Real.transitionReciprocalGap y))
      (Real.transitionLogisticFirstDerivative x) x := by
  unfold Real.transitionLogisticFirstDerivative
  exact (Real.hasDerivAt_decreasingLogistic
    (Real.transitionReciprocalGap x)).comp x
      (Real.hasDerivAt_transitionReciprocalGap hx0 hx1)

theorem Real.hasDerivAt_transitionLogisticFirstDerivative
    {x : ℝ}
    (hx0 : x ≠ 0)
    (hx1 : 1 - x ≠ 0) :
    HasDerivAt Real.transitionLogisticFirstDerivative
      (Real.transitionLogisticSecondDerivative x) x := by
  unfold Real.transitionLogisticFirstDerivative
  unfold Real.transitionLogisticSecondDerivative
  have houter :=
    (Real.hasDerivAt_decreasingLogisticDerivative
      (Real.transitionReciprocalGap x)).comp x
        (Real.hasDerivAt_transitionReciprocalGap hx0 hx1)
  have hinner := Real.hasDerivAt_transitionGapDerivative hx0 hx1
  exact houter.mul hinner

end
end LFunctions
end Boundary
