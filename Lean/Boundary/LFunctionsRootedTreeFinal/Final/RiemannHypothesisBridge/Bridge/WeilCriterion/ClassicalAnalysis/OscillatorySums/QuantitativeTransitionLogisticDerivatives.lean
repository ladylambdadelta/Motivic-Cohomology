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

theorem Real.transition_neg_one_div_square_normalization
    (a : ℝ) :
    -1 / a ^ 2 = -(a⁻¹ ^ 2) := by
  exact Eq.trans
    (div_eq_mul_inv (-1) (a ^ 2))
    (Eq.trans
      (neg_one_mul (a ^ 2)⁻¹)
      (congrArg Neg.neg (inv_pow a 2).symm))

theorem Real.transition_one_div_square_normalization
    (a : ℝ) :
    1 / a ^ 2 = a⁻¹ ^ 2 := by
  exact Eq.trans
    (one_div (a ^ 2))
    (inv_pow a 2).symm

theorem Real.transition_negated_neg_one_div_square_normalization
    (a : ℝ) :
    -(-1) / a ^ 2 = a⁻¹ ^ 2 := by
  exact Eq.trans
    (congrArg (fun numerator : ℝ => numerator / a ^ 2)
      (neg_neg (1 : ℝ)))
    (Real.transition_one_div_square_normalization a)

theorem Real.transition_neg_sub_eq_neg_add
    (a b : ℝ) :
    -a - b = -(a + b) := by
  exact Eq.trans
    (sub_eq_add_neg (-a) b)
    (neg_add a b).symm

theorem Real.transition_base_mul_square_eq_cube
    (a : ℝ) :
    a * a ^ 2 = a ^ 3 := by
  exact Eq.trans
    (congrArg (fun value : ℝ => a * value) (pow_two a))
    (pow_three a).symm

theorem Real.transition_left_energy_derivative_normalization
    (a : ℝ) :
    2 * a ^ (2 - 1) * (-(a ^ 2)) = -2 * a ^ 3 := by
  have hpower : a ^ (2 - 1) = a := pow_one a
  calc
    2 * a ^ (2 - 1) * (-(a ^ 2)) =
        2 * a * (-(a ^ 2)) :=
      congrArg (fun value : ℝ => 2 * value * (-(a ^ 2))) hpower
    _ = -((2 * a) * a ^ 2) :=
      mul_neg (2 * a) (a ^ 2)
    _ = -(2 * (a * a ^ 2)) :=
      congrArg Neg.neg (mul_assoc 2 a (a ^ 2))
    _ = -(2 * a ^ 3) :=
      congrArg Neg.neg
        (congrArg (fun value : ℝ => 2 * value)
          (Real.transition_base_mul_square_eq_cube a))
    _ = -2 * a ^ 3 :=
      (neg_mul 2 (a ^ 3)).symm

theorem Real.transition_right_energy_derivative_normalization
    (a : ℝ) :
    2 * a ^ (2 - 1) * a ^ 2 = 2 * a ^ 3 := by
  have hpower : a ^ (2 - 1) = a := pow_one a
  calc
    2 * a ^ (2 - 1) * a ^ 2 = 2 * a * a ^ 2 :=
      congrArg (fun value : ℝ => 2 * value * a ^ 2) hpower
    _ = 2 * (a * a ^ 2) :=
      mul_assoc 2 a (a ^ 2)
    _ = 2 * a ^ 3 :=
      congrArg (fun value : ℝ => 2 * value)
        (Real.transition_base_mul_square_eq_cube a)

theorem Real.transitionReciprocalGap_eq
    (x : ℝ) :
    Real.transitionReciprocalGap x = x⁻¹ - (1 - x)⁻¹ := by
  rfl

theorem Real.hasDerivAt_transitionLeftReciprocal
    {x : ℝ}
    (hx : x ≠ 0) :
    HasDerivAt Real.transitionLeftReciprocal (-(x⁻¹ ^ 2)) x := by
  unfold Real.transitionLeftReciprocal
  have hraw := (hasDerivAt_id x).inv hx
  have hnormalize :=
    Real.transition_neg_one_div_square_normalization x
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => y⁻¹) value x)
    hnormalize
    hraw

theorem Real.hasDerivAt_transitionRightReciprocal
    {x : ℝ}
    (hx : 1 - x ≠ 0) :
    HasDerivAt Real.transitionRightReciprocal ((1 - x)⁻¹ ^ 2) x := by
  unfold Real.transitionRightReciprocal
  have hinnerRaw := (hasDerivAt_const x 1).sub (hasDerivAt_id x)
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x :=
    Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => 1 - y) value x)
      (zero_sub (1 : ℝ))
      hinnerRaw
  have hinverse := hinner.inv hx
  have hnormalize :=
    Real.transition_negated_neg_one_div_square_normalization (1 - x)
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
    exact Real.transition_neg_sub_eq_neg_add
      (x⁻¹ ^ 2) ((1 - x)⁻¹ ^ 2)
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
    exact congrArg₂ (fun first second : ℝ => first + second)
      (Real.transition_left_energy_derivative_normalization x⁻¹)
      (Real.transition_right_energy_derivative_normalization (1 - x)⁻¹)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ => y⁻¹ ^ 2 + (1 - y)⁻¹ ^ 2) value x)
    hnormalize
    hsum

theorem Real.transition_cubic_first_cross_normalization
    (p q : ℝ) :
    p * (p * q) = q * p ^ 2 := by
  exact Eq.trans
    (mul_assoc p p q).symm
    (Eq.trans
      (congrArg (fun value : ℝ => value * q) (pow_two p).symm)
      (mul_comm (p ^ 2) q))

theorem Real.transition_cubic_second_cross_normalization
    (p q : ℝ) :
    p * q ^ 2 = q * (p * q) := by
  exact Eq.trans
    (congrArg (fun value : ℝ => p * value) (pow_two q))
    (Eq.trans
      (mul_assoc p q q).symm
      (Eq.trans
        (congrArg (fun value : ℝ => value * q) (mul_comm p q))
        (mul_assoc q p q)))

theorem Real.transition_cubic_cross_terms_cancel
    (p q : ℝ) :
    (p ^ 3 + q * p ^ 2 + q * (p * q)) -
        (q * p ^ 2 + q * (p * q) + q ^ 3) =
      p ^ 3 - q ^ 3 := by
  have hleft :
      p ^ 3 + q * p ^ 2 + q * (p * q) =
        (q * p ^ 2 + q * (p * q)) + p ^ 3 := by
    exact Eq.trans
      (add_assoc (p ^ 3) (q * p ^ 2) (q * (p * q)))
      (add_comm (p ^ 3) (q * p ^ 2 + q * (p * q)))
  exact Eq.trans
    (congrArg
      (fun value : ℝ =>
        value - (q * p ^ 2 + q * (p * q) + q ^ 3))
      hleft)
    (add_sub_add_left_eq_sub (p ^ 3) (q ^ 3)
      (q * p ^ 2 + q * (p * q)))

theorem Real.transition_cubic_difference_factorization
    (p q : ℝ) :
    (p - q) * (p ^ 2 + p * q + q ^ 2) =
      p ^ 3 - q ^ 3 := by
  have hpExpand :
      p * (p ^ 2 + p * q + q ^ 2) =
        p * p ^ 2 + p * (p * q) + p * q ^ 2 := by
    exact Eq.trans
      (mul_add p (p ^ 2 + p * q) (q ^ 2))
      (congrArg (fun value : ℝ => value + p * q ^ 2)
        (mul_add p (p ^ 2) (p * q)))
  have hqExpand :
      q * (p ^ 2 + p * q + q ^ 2) =
        q * p ^ 2 + q * (p * q) + q * q ^ 2 := by
    exact Eq.trans
      (mul_add q (p ^ 2 + p * q) (q ^ 2))
      (congrArg (fun value : ℝ => value + q * q ^ 2)
        (mul_add q (p ^ 2) (p * q)))
  have hpNormalize :
      p * p ^ 2 + p * (p * q) + p * q ^ 2 =
        p ^ 3 + q * p ^ 2 + q * (p * q) := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      (congrArg₂ (fun first second : ℝ => first + second)
        (Real.transition_base_mul_square_eq_cube p)
        (Real.transition_cubic_first_cross_normalization p q))
      (Real.transition_cubic_second_cross_normalization p q)
  have hqNormalize :
      q * p ^ 2 + q * (p * q) + q * q ^ 2 =
        q * p ^ 2 + q * (p * q) + q ^ 3 := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      rfl
      (Real.transition_base_mul_square_eq_cube q)
  calc
    (p - q) * (p ^ 2 + p * q + q ^ 2) =
        p * (p ^ 2 + p * q + q ^ 2) -
          q * (p ^ 2 + p * q + q ^ 2) :=
      sub_mul p q _
    _ = (p * p ^ 2 + p * (p * q) + p * q ^ 2) -
        (q * p ^ 2 + q * (p * q) + q * q ^ 2) :=
      congrArg₂ (fun first second : ℝ => first - second)
        hpExpand hqExpand
    _ = (p ^ 3 + q * p ^ 2 + q * (p * q)) -
        (q * p ^ 2 + q * (p * q) + q ^ 3) :=
      congrArg₂ (fun first second : ℝ => first - second)
        hpNormalize hqNormalize
    _ = p ^ 3 - q ^ 3 :=
      Real.transition_cubic_cross_terms_cancel p q

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
  calc
    2 * (p - q) * (p ^ 2 + p * q + q ^ 2) =
        2 * ((p - q) * (p ^ 2 + p * q + q ^ 2)) :=
      mul_assoc 2 (p - q) (p ^ 2 + p * q + q ^ 2)
    _ = 2 * (p ^ 3 - q ^ 3) :=
      congrArg (fun value : ℝ => 2 * value)
        (Real.transition_cubic_difference_factorization p q)
    _ = 2 * p ^ 3 - 2 * q ^ 3 :=
      mul_sub 2 (p ^ 3) (q ^ 3)

theorem Real.transition_negated_energy_derivative_normalization
    (p q : ℝ) :
    -(-2 * p ^ 3 + 2 * q ^ 3) =
      2 * p ^ 3 - 2 * q ^ 3 := by
  have hfirst : -(-2 * p ^ 3) = 2 * p ^ 3 := by
    exact Eq.trans
      (congrArg Neg.neg (neg_mul 2 (p ^ 3)))
      (neg_neg (2 * p ^ 3))
  exact Eq.trans
    (neg_add (-2 * p ^ 3) (2 * q ^ 3))
    (Eq.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        hfirst rfl)
      (sub_eq_add_neg (2 * p ^ 3) (2 * q ^ 3)).symm)

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
      (Real.transition_negated_energy_derivative_normalization
        x⁻¹ (1 - x)⁻¹)
      (Real.transitionGapSecondDerivative_eq_cubic_difference x).symm
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => -Real.transitionReciprocalEnergy y)
        value x)
    hnormalize
    hnegative

theorem Real.decreasingLogistic_inverse_derivative_normalization
    (a u : ℝ) :
    -a / u ^ 2 = -(a * u⁻¹ ^ 2) := by
  calc
    -a / u ^ 2 = -a * (u ^ 2)⁻¹ :=
      div_eq_mul_inv (-a) (u ^ 2)
    _ = -a * u⁻¹ ^ 2 :=
      congrArg (fun value : ℝ => -a * value) (inv_pow u 2).symm
    _ = -(a * u⁻¹ ^ 2) :=
      neg_mul a (u⁻¹ ^ 2)

theorem Real.transition_square_derivative_power_normalization
    (a : ℝ) :
    a ^ (2 - 1) = a := by
  exact pow_one a

theorem Real.decreasingLogistic_inverse_cube_collapse
    (u : ℝ)
    (hu : u ≠ 0) :
    u⁻¹ ^ 3 * u = u⁻¹ ^ 2 := by
  have hinverse : u⁻¹ * u = 1 := inv_mul_cancel₀ hu
  calc
    u⁻¹ ^ 3 * u = (u⁻¹ ^ 2 * u⁻¹) * u :=
      congrArg (fun value : ℝ => value * u) (pow_succ u⁻¹ 2)
    _ = u⁻¹ ^ 2 * (u⁻¹ * u) :=
      mul_assoc (u⁻¹ ^ 2) u⁻¹ u
    _ = u⁻¹ ^ 2 * 1 :=
      congrArg (fun value : ℝ => u⁻¹ ^ 2 * value) hinverse
    _ = u⁻¹ ^ 2 :=
      mul_one (u⁻¹ ^ 2)

theorem Real.decreasingLogistic_mixed_product_reassociation
    (e v : ℝ) :
    v * (e * v ^ 2) = e * (v * v ^ 2) := by
  exact Eq.trans
    (mul_assoc v e (v ^ 2)).symm
    (Eq.trans
      (congrArg (fun value : ℝ => value * v ^ 2) (mul_comm v e))
      (mul_assoc e v (v ^ 2)))

theorem Real.decreasingLogistic_positive_cubic_monomial
    (e v : ℝ) :
    e * (2 * v * (e * v ^ 2)) =
      2 * e ^ 2 * v ^ 3 := by
  calc
    e * (2 * v * (e * v ^ 2)) =
        (e * (2 * v)) * (e * v ^ 2) :=
      (mul_assoc e (2 * v) (e * v ^ 2)).symm
    _ = ((2 * e) * v) * (e * v ^ 2) :=
      congrArg (fun value : ℝ => value * (e * v ^ 2))
        (Eq.trans
          (mul_assoc e 2 v).symm
          (congrArg (fun value : ℝ => value * v) (mul_comm e 2)))
    _ = (2 * e) * (v * (e * v ^ 2)) :=
      mul_assoc (2 * e) v (e * v ^ 2)
    _ = (2 * e) * (e * (v * v ^ 2)) :=
      congrArg (fun value : ℝ => (2 * e) * value)
        (Real.decreasingLogistic_mixed_product_reassociation e v)
    _ = (2 * e) * (e * v ^ 3) :=
      congrArg (fun value : ℝ => (2 * e) * (e * value))
        (Real.transition_base_mul_square_eq_cube v)
    _ = ((2 * e) * e) * v ^ 3 :=
      (mul_assoc (2 * e) e (v ^ 3)).symm
    _ = (2 * (e * e)) * v ^ 3 :=
      congrArg (fun value : ℝ => value * v ^ 3) (mul_assoc 2 e e)
    _ = 2 * e ^ 2 * v ^ 3 :=
      congrArg (fun value : ℝ => 2 * value * v ^ 3) (pow_two e).symm

theorem Real.decreasingLogistic_negative_cubic_monomial
    (e v : ℝ) :
    e * (2 * v * (-(e * v ^ 2))) =
      -(2 * e ^ 2 * v ^ 3) := by
  calc
    e * (2 * v * (-(e * v ^ 2))) =
        e * (-((2 * v) * (e * v ^ 2))) :=
      congrArg (fun value : ℝ => e * value)
        (mul_neg (2 * v) (e * v ^ 2))
    _ = -(e * ((2 * v) * (e * v ^ 2))) :=
      mul_neg e ((2 * v) * (e * v ^ 2))
    _ = -(2 * e ^ 2 * v ^ 3) :=
      congrArg Neg.neg
        (Real.decreasingLogistic_positive_cubic_monomial e v)

theorem Real.decreasingLogistic_raw_sum_normalization
    (e v : ℝ) :
    -(e * v ^ 2 + e * (2 * v * (-(e * v ^ 2)))) =
      -(e * v ^ 2) + 2 * e ^ 2 * v ^ 3 := by
  let A := e * v ^ 2
  let C := 2 * e ^ 2 * v ^ 3
  change -(A + e * (2 * v * (-A))) = -A + C
  have hnegative : e * (2 * v * (-A)) = -C :=
    Real.decreasingLogistic_negative_cubic_monomial e v
  calc
    -(A + e * (2 * v * (-A))) = -(A + -C) :=
      congrArg Neg.neg
        (congrArg (fun value : ℝ => A + value) hnegative)
    _ = -(A - C) :=
      congrArg Neg.neg (sub_eq_add_neg A C).symm
    _ = C - A :=
      neg_sub A C
    _ = C + -A :=
      sub_eq_add_neg C A
    _ = -A + C :=
      add_comm C (-A)

theorem Real.decreasingLogistic_quadratic_cubic_reassociation
    (e v : ℝ) :
    2 * e ^ 2 * v ^ 3 =
      (e * v ^ 3) * (2 * e) := by
  calc
    2 * e ^ 2 * v ^ 3 = 2 * (e * e) * v ^ 3 :=
      congrArg (fun value : ℝ => 2 * value * v ^ 3) (pow_two e)
    _ = ((2 * e) * e) * v ^ 3 :=
      congrArg (fun value : ℝ => value * v ^ 3) (mul_assoc 2 e e).symm
    _ = (2 * e) * (e * v ^ 3) :=
      mul_assoc (2 * e) e (v ^ 3)
    _ = (e * v ^ 3) * (2 * e) :=
      mul_comm (2 * e) (e * v ^ 3)

theorem Real.decreasingLogistic_second_derivative_factorization
    (e u : ℝ)
    (hu : u ≠ 0) :
    -(e * u⁻¹ ^ 2) + 2 * e ^ 2 * u⁻¹ ^ 3 =
      (e * u⁻¹ ^ 3) * (-u + 2 * e) := by
  have hcollapse :=
    Real.decreasingLogistic_inverse_cube_collapse u hu
  have hfirst :
      -(e * u⁻¹ ^ 2) = (e * u⁻¹ ^ 3) * (-u) := by
    have hproduct : (e * u⁻¹ ^ 3) * u = e * u⁻¹ ^ 2 := by
      exact Eq.trans
        (mul_assoc e (u⁻¹ ^ 3) u)
        (congrArg (fun value : ℝ => e * value) hcollapse)
    exact Eq.trans
      (congrArg Neg.neg hproduct.symm)
      (mul_neg (e * u⁻¹ ^ 3) u).symm
  have hsecond :
      2 * e ^ 2 * u⁻¹ ^ 3 =
        (e * u⁻¹ ^ 3) * (2 * e) :=
    Real.decreasingLogistic_quadratic_cubic_reassociation e u⁻¹
  exact Eq.trans
    (congrArg₂ (fun first second : ℝ => first + second)
      hfirst hsecond)
    (mul_add (e * u⁻¹ ^ 3) (-u) (2 * e)).symm

theorem Real.decreasingLogistic_bracket_normalization
    (e : ℝ) :
    -(1 + e) + 2 * e = e - 1 := by
  have hnegative : -(1 + e) = -1 + -e := by
    exact Eq.trans
      (neg_add_rev 1 e)
      (add_comm (-e) (-1))
  calc
    -(1 + e) + 2 * e = (-1 + -e) + (e + e) :=
      congrArg₂ (fun first second : ℝ => first + second)
        hnegative (two_mul e)
    _ = -1 + (-e + (e + e)) :=
      add_assoc (-1) (-e) (e + e)
    _ = -1 + ((-e + e) + e) :=
      congrArg (fun value : ℝ => -1 + value)
        (add_assoc (-e) e e).symm
    _ = -1 + (0 + e) :=
      congrArg (fun value : ℝ => -1 + (value + e))
        (neg_add_cancel e)
    _ = -1 + e :=
      congrArg (fun value : ℝ => -1 + value) (zero_add e)
    _ = e + -1 :=
      add_comm (-1) e
    _ = e - 1 :=
      (sub_eq_add_neg e 1).symm

theorem Real.decreasingLogistic_factor_order_normalization
    (e v : ℝ) :
    (e * v ^ 3) * (e - 1) =
      e * (e - 1) * v ^ 3 := by
  exact Eq.trans
    (mul_assoc e (v ^ 3) (e - 1))
    (Eq.trans
      (congrArg (fun value : ℝ => e * value)
        (mul_comm (v ^ 3) (e - 1)))
      (mul_assoc e (e - 1) (v ^ 3)).symm)

theorem Real.hasDerivAt_decreasingLogistic
    (z : ℝ) :
    HasDerivAt Real.decreasingLogistic
      (Real.decreasingLogisticDerivative z) z := by
  unfold Real.decreasingLogistic
  unfold Real.decreasingLogisticDerivative
  have hinnerRaw :=
    (hasDerivAt_const z 1).add (Real.hasDerivAt_exp z)
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + Real.exp y) (Real.exp z) z :=
    Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => 1 + Real.exp y) value z)
      (zero_add (Real.exp z))
      hinnerRaw
  have hne : 1 + Real.exp z ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos z))
  have hinverse := hinner.inv hne
  have hnormalize :=
    Real.decreasingLogistic_inverse_derivative_normalization
      (Real.exp z) (1 + Real.exp z)
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹) value z)
    hnormalize
    hinverse

theorem Real.hasDerivAt_decreasingLogisticDerivative
    (z : ℝ) :
    HasDerivAt Real.decreasingLogisticDerivative
      (Real.decreasingLogisticSecondDerivative z) z := by
  let e := Real.exp z
  let u := 1 + e
  let v := u⁻¹
  have he : HasDerivAt Real.exp e z := Real.hasDerivAt_exp z
  have huRaw := (hasDerivAt_const z 1).add he
  have hu : HasDerivAt (fun y : ℝ => 1 + Real.exp y) e z :=
    Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => 1 + Real.exp y) value z)
      (zero_add e)
      huRaw
  have huNe : u ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos zero_le_one (Real.exp_pos z))
  have huInvRaw := hu.inv huNe
  have huInv : HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹)
      (-(e * v ^ 2)) z :=
    Eq.subst
      (motive := fun value : ℝ =>
        HasDerivAt (fun y : ℝ => (1 + Real.exp y)⁻¹) value z)
      (Real.decreasingLogistic_inverse_derivative_normalization e u)
      huInvRaw
  have huInvSq := huInv.pow 2
  have hproduct := he.mul huInvSq
  have hnegative := hproduct.neg
  unfold Real.decreasingLogisticDerivative
  unfold Real.decreasingLogisticSecondDerivative
  change HasDerivAt
    (fun y : ℝ => -(Real.exp y * (1 + Real.exp y)⁻¹ ^ 2))
    (e * (e - 1) * v ^ 3) z
  have hraw :
      HasDerivAt
        (fun y : ℝ => -(Real.exp y * (1 + Real.exp y)⁻¹ ^ 2))
        (-(e * v ^ 2 +
          e * (2 * v ^ (2 - 1) * (-(e * v ^ 2))))) z :=
    hnegative
  have hpower :=
    Real.transition_square_derivative_power_normalization v
  have hbracket : -u + 2 * e = e - 1 :=
    Real.decreasingLogistic_bracket_normalization e
  have hnormalize :
      -(e * v ^ 2 +
          e * (2 * v ^ (2 - 1) * (-(e * v ^ 2)))) =
        e * (e - 1) * v ^ 3 := by
    calc
      -(e * v ^ 2 +
          e * (2 * v ^ (2 - 1) * (-(e * v ^ 2)))) =
          -(e * v ^ 2 +
            e * (2 * v * (-(e * v ^ 2)))) :=
        congrArg Neg.neg
          (congrArg (fun value : ℝ => e * v ^ 2 +
            e * (2 * value * (-(e * v ^ 2)))) hpower)
      _ = -(e * v ^ 2) + 2 * e ^ 2 * v ^ 3 :=
        Real.decreasingLogistic_raw_sum_normalization e v
      _ = (e * v ^ 3) * (-u + 2 * e) :=
        Real.decreasingLogistic_second_derivative_factorization e u huNe
      _ = (e * v ^ 3) * (e - 1) :=
        congrArg (fun value : ℝ => (e * v ^ 3) * value) hbracket
      _ = e * (e - 1) * v ^ 3 :=
        Real.decreasingLogistic_factor_order_normalization e v
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

theorem Real.transition_product_rule_square_normalization
    (outer inner : ℝ) :
    outer * inner * inner = outer * inner ^ 2 := by
  exact Eq.trans
    (mul_assoc outer inner inner)
    (congrArg (fun value : ℝ => outer * value) (pow_two inner).symm)

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
  have hraw := houter.mul hinner
  have hnormalize :
      Real.decreasingLogisticSecondDerivative
            (Real.transitionReciprocalGap x) *
          Real.transitionGapDerivative x *
          Real.transitionGapDerivative x +
        Real.decreasingLogisticDerivative
            (Real.transitionReciprocalGap x) *
          Real.transitionGapSecondDerivative x =
      Real.decreasingLogisticSecondDerivative
            (Real.transitionReciprocalGap x) *
          Real.transitionGapDerivative x ^ 2 +
        Real.decreasingLogisticDerivative
            (Real.transitionReciprocalGap x) *
          Real.transitionGapSecondDerivative x := by
    exact congrArg₂ (fun first second : ℝ => first + second)
      (Real.transition_product_rule_square_normalization
        (Real.decreasingLogisticSecondDerivative
          (Real.transitionReciprocalGap x))
        (Real.transitionGapDerivative x))
      rfl
  exact Eq.subst
    (motive := fun value : ℝ =>
      HasDerivAt
        (fun y : ℝ =>
          Real.decreasingLogisticDerivative
              (Real.transitionReciprocalGap y) *
            Real.transitionGapDerivative y)
        value x)
    hnormalize
    hraw

end
end LFunctions
end Boundary
