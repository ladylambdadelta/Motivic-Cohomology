import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeLogisticLowerBound

/-!
# Reciprocal coordinates for transition convexity

On the open transition interval set `p=x⁻¹` and `q=(1-x)⁻¹`.  Complementarity
gives the decisive relation `p*q=p+q`.  This owner records the positivity,
ordering, and symmetric-polynomial identities used in the curvature sign
calculation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.transitionLeftReciprocal (x : ℝ) : ℝ := x⁻¹

def Real.transitionRightReciprocal (x : ℝ) : ℝ := (1 - x)⁻¹

def Real.transitionReciprocalSum (x : ℝ) : ℝ :=
  Real.transitionLeftReciprocal x +
    Real.transitionRightReciprocal x

def Real.transitionReciprocalGap (x : ℝ) : ℝ :=
  Real.transitionLeftReciprocal x -
    Real.transitionRightReciprocal x

def Real.transitionReciprocalEnergy (x : ℝ) : ℝ :=
  Real.transitionLeftReciprocal x ^ 2 +
    Real.transitionRightReciprocal x ^ 2

def Real.transitionReciprocalCubicSum (x : ℝ) : ℝ :=
  Real.transitionLeftReciprocal x ^ 2 +
    Real.transitionLeftReciprocal x *
      Real.transitionRightReciprocal x +
    Real.transitionRightReciprocal x ^ 2

theorem Real.transitionLeftReciprocal_pos
    {x : ℝ}
    (hx : 0 < x) :
    0 < Real.transitionLeftReciprocal x := by
  unfold Real.transitionLeftReciprocal
  exact inv_pos.mpr hx

theorem Real.transitionRightReciprocal_pos
    {x : ℝ}
    (hx : x < 1) :
    0 < Real.transitionRightReciprocal x := by
  unfold Real.transitionRightReciprocal
  exact inv_pos.mpr (sub_pos.mpr hx)

theorem Real.transitionReciprocalSum_pos
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    0 < Real.transitionReciprocalSum x := by
  unfold Real.transitionReciprocalSum
  exact add_pos
    (Real.transitionLeftReciprocal_pos hx0)
    (Real.transitionRightReciprocal_pos hx1)

theorem Real.transition_left_le_right_complement
    {x : ℝ}
    (hx : x ≤ 1 / 2) :
    x ≤ 1 - x := by
  have htwoPos : (0 : ℝ) < 2 := zero_lt_two
  have hdouble : 2 * x ≤ 1 := by
    have hscaled := mul_le_mul_of_nonneg_left hx (le_of_lt htwoPos)
    have hright : (2 : ℝ) * (1 / 2) = 1 := by
      exact mul_one_div_cancel (two_ne_zero)
    exact le_trans hscaled (le_of_eq hright)
  exact (le_sub_iff_add_le).mpr
    (Eq.subst
      (motive := fun value : ℝ => value ≤ 1)
      (two_mul x).symm
      hdouble)

theorem Real.transitionRightReciprocal_le_left
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    Real.transitionRightReciprocal x ≤
      Real.transitionLeftReciprocal x := by
  have hxComplement := Real.transition_left_le_right_complement hxHalf
  have hcomplementPos : 0 < 1 - x :=
    lt_of_lt_of_le hx0 hxComplement
  unfold Real.transitionRightReciprocal
  unfold Real.transitionLeftReciprocal
  exact (inv_le_inv₀ hx0 hcomplementPos).mpr hxComplement

theorem Real.transitionReciprocalGap_nonneg
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    0 ≤ Real.transitionReciprocalGap x := by
  unfold Real.transitionReciprocalGap
  exact sub_nonneg.mpr
    (Real.transitionRightReciprocal_le_left hx0 hxHalf)

theorem Real.transition_complement_nonzero
    {x : ℝ}
    (hx : x < 1) :
    1 - x ≠ 0 := by
  exact ne_of_gt (sub_pos.mpr hx)

theorem Real.transitionReciprocal_product_eq_sum
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionLeftReciprocal x *
        Real.transitionRightReciprocal x =
      Real.transitionReciprocalSum x := by
  have hxNe : x ≠ 0 := ne_of_gt hx0
  have hcomplementNe : 1 - x ≠ 0 :=
    Real.transition_complement_nonzero hx1
  unfold Real.transitionLeftReciprocal
  unfold Real.transitionRightReciprocal
  unfold Real.transitionReciprocalSum
  have hinverseAdd := inv_add_inv hxNe hcomplementNe
  have hsum : x + (1 - x) = 1 := by
    exact add_sub_cancel_left x 1
  have hproductInverse : x⁻¹ * (1 - x)⁻¹ =
      (x * (1 - x))⁻¹ := by
    exact (mul_inv_rev₀ x (1 - x)).symm
  have hquotient :
      (x + (1 - x)) / (x * (1 - x)) =
        (x * (1 - x))⁻¹ := by
    exact Eq.trans
      (congrArg
        (fun numerator : ℝ => numerator / (x * (1 - x))) hsum)
      (one_div (x * (1 - x)))
  exact Eq.trans hproductInverse
    (Eq.trans hquotient.symm hinverseAdd.symm)

theorem Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionReciprocalEnergy x =
      Real.transitionReciprocalSum x ^ 2 -
        2 * Real.transitionReciprocalSum x := by
  let p := Real.transitionLeftReciprocal x
  let q := Real.transitionRightReciprocal x
  have hpq : p * q = Real.transitionReciprocalSum x :=
    Real.transitionReciprocal_product_eq_sum hx0 hx1
  unfold Real.transitionReciprocalEnergy
  unfold Real.transitionReciprocalSum
  change p ^ 2 + q ^ 2 = (p + q) ^ 2 - 2 * (p + q)
  have hsquare : (p + q) ^ 2 = p ^ 2 + 2 * (p * q) + q ^ 2 := by
    calc
      (p + q) ^ 2 = (p + q) * (p + q) := pow_two (p + q)
      _ = p * p + p * q + (q * p + q * q) := by
        exact (mul_add (p + q) p q).trans
          (congrArg₂ (fun first second : ℝ => first + second)
            (add_mul p q p) (add_mul p q q))
      _ = p ^ 2 + 2 * (p * q) + q ^ 2 := by
        exact congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            (pow_two p).symm
            ((congrArg₂ (fun first second : ℝ => first + second)
              rfl (mul_comm q p)).trans (two_mul (p * q)).symm))
          (pow_two q).symm
  have htwice : 2 * (p + q) = 2 * (p * q) :=
    congrArg (fun value : ℝ => 2 * value) hpq.symm
  calc
    p ^ 2 + q ^ 2 =
        (p ^ 2 + 2 * (p * q) + q ^ 2) - 2 * (p * q) := by
      let middle := 2 * (p * q)
      calc
        p ^ 2 + q ^ 2 = p ^ 2 + (middle - middle) + q ^ 2 := by
          exact congrArg
            (fun value : ℝ => p ^ 2 + value + q ^ 2)
            (sub_self middle).symm
        _ = (p ^ 2 + middle + q ^ 2) - middle := by
          exact
            (add_assoc (p ^ 2) (middle - middle) (q ^ 2)).trans
              ((congrArg (fun value : ℝ => p ^ 2 + value)
                ((sub_add_eq_add_sub middle middle (q ^ 2)).trans
                  (congrArg (fun value : ℝ => value - middle)
                    (add_comm middle (q ^ 2))))).trans
                (add_sub_assoc (p ^ 2) (middle + q ^ 2) middle))
    _ = (p + q) ^ 2 - 2 * (p * q) :=
      congrArg (fun value : ℝ => value - 2 * (p * q)) hsquare.symm
    _ = (p + q) ^ 2 - 2 * (p + q) :=
      congrArg (fun value : ℝ => (p + q) ^ 2 - value) htwice.symm

theorem Real.transitionReciprocalCubicSum_eq_sum_mul_sum_sub_one
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionReciprocalCubicSum x =
      Real.transitionReciprocalSum x *
        (Real.transitionReciprocalSum x - 1) := by
  have henergy :=
    Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum hx0 hx1
  have hproduct :=
    Real.transitionReciprocal_product_eq_sum hx0 hx1
  unfold Real.transitionReciprocalCubicSum
  unfold Real.transitionReciprocalEnergy at henergy
  let p := Real.transitionLeftReciprocal x
  let q := Real.transitionRightReciprocal x
  let s := Real.transitionReciprocalSum x
  change p ^ 2 + p * q + q ^ 2 = s * (s - 1)
  have hleft : p ^ 2 + p * q + q ^ 2 =
      (p ^ 2 + q ^ 2) + p * q := by
    exact (add_assoc (p ^ 2) (p * q) (q ^ 2)).trans
      (congrArg (fun value : ℝ => p ^ 2 + value)
        (add_comm (p * q) (q ^ 2))).trans
      (add_assoc (p ^ 2) (q ^ 2) (p * q)).symm
  have hright : s * (s - 1) = s ^ 2 - s := by
    exact (mul_sub s s 1).trans
      (congrArg₂ (fun first second : ℝ => first - second)
        (pow_two s).symm (mul_one s))
  have hcombine : (s ^ 2 - 2 * s) + s = s ^ 2 - s := by
    have htwo : 2 * s = s + s := two_mul s
    calc
      (s ^ 2 - 2 * s) + s = (s ^ 2 - (s + s)) + s :=
        congrArg (fun value : ℝ => (s ^ 2 - value) + s) htwo
      _ = (s ^ 2 - s - s) + s :=
        congrArg (fun value : ℝ => value + s)
          (sub_add_eq_sub_sub (s ^ 2) s s)
      _ = s ^ 2 - s := sub_add_cancel (s ^ 2 - s) s
  exact Eq.trans hleft
    (Eq.trans
      (congrArg₂ (fun first second : ℝ => first + second)
        henergy hproduct)
      (Eq.trans hcombine hright.symm))

theorem Real.twice_reciprocal_product_le_energy
    (p q : ℝ) :
    2 * (p * q) ≤ p ^ 2 + q ^ 2 := by
  have hsquare : 0 ≤ (p - q) ^ 2 := sq_nonneg (p - q)
  have hidentity :
      (p - q) ^ 2 = p ^ 2 + q ^ 2 - 2 * (p * q) := by
    calc
      (p - q) ^ 2 = (p - q) * (p - q) := pow_two (p - q)
      _ = p * p - p * q - (q * p - q * q) := by
        exact (mul_sub (p - q) p q).trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (sub_mul p q p) (sub_mul p q q))
      _ = p ^ 2 - p * q - (p * q - q ^ 2) := by
        exact congrArg₂ (fun first second : ℝ => first - second)
          (congrArg₂ (fun first second : ℝ => first - second)
            (pow_two p).symm rfl)
          (congrArg₂ (fun first second : ℝ => first - second)
            (mul_comm q p) (pow_two q).symm)
      _ = p ^ 2 + q ^ 2 - 2 * (p * q) := by
        let product := p * q
        calc
          p ^ 2 - product - (product - q ^ 2) =
              p ^ 2 - product - product + q ^ 2 :=
            sub_sub_sub_cancel_right (p ^ 2 - product) product (q ^ 2)
          _ = (p ^ 2 + q ^ 2) - (product + product) := by
            exact
              (sub_add_eq_add_sub (p ^ 2 - product - product) (q ^ 2)
                (product + product)).symm.trans
              (congrArg₂ (fun first second : ℝ => first - second)
                (add_comm (p ^ 2) (q ^ 2))
                rfl)
          _ = p ^ 2 + q ^ 2 - 2 * product :=
            congrArg (fun value : ℝ => p ^ 2 + q ^ 2 - value)
              (two_mul product).symm
  have hdifference : 0 ≤ p ^ 2 + q ^ 2 - 2 * (p * q) :=
    Eq.subst (motive := fun value : ℝ => 0 ≤ value)
      hidentity.symm hsquare
  exact sub_nonneg.mp hdifference

theorem Real.four_le_transitionReciprocalSum
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    4 ≤ Real.transitionReciprocalSum x := by
  let p := Real.transitionLeftReciprocal x
  let q := Real.transitionRightReciprocal x
  let s := Real.transitionReciprocalSum x
  have hsPos : 0 < s := Real.transitionReciprocalSum_pos hx0 hx1
  have hpq : p * q = s :=
    Real.transitionReciprocal_product_eq_sum hx0 hx1
  have henergy :=
    Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum hx0 hx1
  have hamgm := Real.twice_reciprocal_product_le_energy p q
  have htwoS : 2 * s ≤ s ^ 2 - 2 * s := by
    exact Eq.subst
      (motive := fun product : ℝ =>
        2 * product ≤ s ^ 2 - 2 * s)
      hpq
      (Eq.subst
        (motive := fun energy : ℝ => 2 * (p * q) ≤ energy)
        henergy
        hamgm)
  have hfourS : 4 * s ≤ s ^ 2 := by
    have hadd := add_le_add_right htwoS (2 * s)
    have hleft : 2 * s + 2 * s = 4 * s := by
      calc
        2 * s + 2 * s = (2 + 2) * s :=
          (add_mul 2 2 s).symm
        _ = 4 * s :=
          congrArg (fun coefficient : ℝ => coefficient * s)
            (show (2 : ℝ) + 2 = 4 from rfl)
    have hright : s ^ 2 - 2 * s + 2 * s = s ^ 2 :=
      sub_add_cancel (s ^ 2) (2 * s)
    exact le_trans (le_of_eq hleft.symm)
      (le_trans hadd (le_of_eq hright))
  have hsquare : s ^ 2 = s * s := pow_two s
  have hproduct : 4 * s ≤ s * s :=
    le_trans hfourS (le_of_eq hsquare)
  exact (mul_le_mul_right hsPos).mp hproduct

end
end LFunctions
end Boundary
