import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionLogisticIdentification
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionCurvatureVariation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeCutoffSecondDerivativeSupport

/-!
# Convexity and concavity of the quantitative transition

The logistic second derivative factors as a nonnegative prefactor times the
curvature bracket controlled by the scalar ratio theorem.  Hence the
transition is convex on the left half and concave on the right half.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.transitionConvexity_four_factor_association
    (first second third fourth : ℝ) :
    first * second * third ^ 3 * fourth =
      (first * third ^ 2 * fourth) * (second * third) := by
  have hcube : third ^ 3 = third ^ 2 * third := pow_succ third 2
  calc
    first * second * third ^ 3 * fourth =
        (first * second) * (third ^ 2 * third) * fourth :=
      congrArg (fun value : ℝ => first * second * value * fourth) hcube
    _ = ((first * third ^ 2) * (second * third)) * fourth :=
      congrArg (fun value : ℝ => value * fourth)
        (mul_mul_mul_comm first second (third ^ 2) third)
    _ = (first * third ^ 2) * ((second * third) * fourth) :=
      mul_assoc (first * third ^ 2) (second * third) fourth
    _ = (first * third ^ 2) * (fourth * (second * third)) :=
      congrArg (fun value : ℝ => (first * third ^ 2) * value)
        (mul_comm (second * third) fourth)
    _ = (first * third ^ 2 * fourth) * (second * third) :=
      (mul_assoc (first * third ^ 2) fourth (second * third)).symm

theorem Real.transitionConvexity_right_factor_commutation
    (first second third : ℝ) :
    first * (second * third) = (first * third) * second := by
  exact Eq.trans
    (mul_assoc first second third).symm
    (mul_right_comm first second third)

theorem Real.transitionConvexity_two_lt_four :
    (2 : ℝ) < 4 := by
  have htwoPositive : (0 : ℝ) < 2 := zero_lt_two
  have hraw : (2 : ℝ) < 2 + 2 :=
    lt_add_of_pos_right 2 htwoPositive
  have hsum : (2 : ℝ) + 2 = 4 :=
    Real.transitionSecondDerivative_natCast_add 2 2 4 rfl
  exact Eq.subst
    (motive := fun upper : ℝ => (2 : ℝ) < upper)
    hsum
    hraw

theorem Real.transitionConvexity_exponentialOddRatio_eq
    (d : ℝ) :
    Real.exponentialOddRatio d =
      (Real.exp d - 1) / (1 + Real.exp d) := by
  unfold Real.exponentialOddRatio
  exact congrArg
    (fun denominator : ℝ => (Real.exp d - 1) / denominator)
    (add_comm (Real.exp d) 1)

theorem Real.transitionReciprocalEnergy_eq_sum_product
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionReciprocalEnergy x =
      Real.transitionReciprocalSum x *
        (Real.transitionReciprocalSum x - 2) := by
  have henergy :=
    Real.transitionReciprocalEnergy_eq_sum_sq_sub_two_sum hx0 hx1
  let s := Real.transitionReciprocalSum x
  have hfactor : s ^ 2 - 2 * s = s * (s - 2) := by
    exact Eq.trans
      (congrArg₂ (fun first second : ℝ => first - second)
        (pow_two s) (mul_comm 2 s))
      (mul_sub s s 2).symm
  exact Eq.trans henergy hfactor

theorem Real.transitionGapSecondDerivative_eq_scalar_numerator
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionGapSecondDerivative x =
      2 * Real.transitionReciprocalGap x *
        (Real.transitionReciprocalSum x *
          (Real.transitionReciprocalSum x - 1)) := by
  unfold Real.transitionGapSecondDerivative
  exact congrArg
    (fun value : ℝ => 2 * Real.transitionReciprocalGap x * value)
    (Real.transitionReciprocalCubicSum_eq_sum_mul_sum_sub_one hx0 hx1)

theorem Real.transitionScalarCurvatureRatio_eq_gapSecond_div_energy_sq
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionScalarCurvatureRatio
        (Real.transitionReciprocalSum x)
        (Real.transitionReciprocalGap x) =
      Real.transitionGapSecondDerivative x /
        Real.transitionReciprocalEnergy x ^ 2 := by
  let s := Real.transitionReciprocalSum x
  let d := Real.transitionReciprocalGap x
  have henergy := Real.transitionReciprocalEnergy_eq_sum_product hx0 hx1
  have hsecond :=
    Real.transitionGapSecondDerivative_eq_scalar_numerator hx0 hx1
  unfold Real.transitionScalarCurvatureRatio
  change (2 * d * s * (s - 1)) / (s ^ 2 * (s - 2) ^ 2) =
    Real.transitionGapSecondDerivative x /
      Real.transitionReciprocalEnergy x ^ 2
  have hnumerator : 2 * d * s * (s - 1) =
      2 * d * (s * (s - 1)) :=
    mul_assoc (2 * d) s (s - 1)
  have hdenominator :
      s ^ 2 * (s - 2) ^ 2 = (s * (s - 2)) ^ 2 := by
    calc
      s ^ 2 * (s - 2) ^ 2 = (s * s) * ((s - 2) * (s - 2)) :=
        congrArg₂ (fun first second : ℝ => first * second)
          (pow_two s) (pow_two (s - 2))
      _ = (s * (s - 2)) * (s * (s - 2)) := by
        exact mul_mul_mul_comm s s (s - 2) (s - 2)
      _ = (s * (s - 2)) ^ 2 := (pow_two _).symm
  exact congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
    (Eq.trans hnumerator hsecond.symm)
    (Eq.trans hdenominator
      (congrArg (fun value : ℝ => value ^ 2) henergy.symm))

theorem Real.transitionLogisticSecondDerivative_factorization
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.transitionLogisticSecondDerivative x =
      Real.transitionLogisticPositiveFactor x *
        Real.transitionLogisticCurvatureBracket x := by
  let d := Real.transitionReciprocalGap x
  let e := Real.exp d
  let u := 1 + e
  let E := Real.transitionReciprocalEnergy x
  let R := Real.transitionScalarCurvatureRatio
    (Real.transitionReciprocalSum x) d
  have henergyPos : 0 < E := by
    have hsum := Real.four_le_transitionReciprocalSum hx0 hx1
    have hsumPos := Real.transitionScalar_pos hsum
    have hsubPos : 0 < Real.transitionReciprocalSum x - 2 := by
      exact sub_pos.mpr (lt_of_lt_of_le
        Real.transitionConvexity_two_lt_four hsum)
    have hidentity := Real.transitionReciprocalEnergy_eq_sum_product hx0 hx1
    exact Eq.subst (motive := fun value : ℝ => 0 < value)
      hidentity.symm (mul_pos hsumPos hsubPos)
  have henergyNe : E ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt henergyPos)
  have hratio :=
    Real.transitionScalarCurvatureRatio_eq_gapSecond_div_energy_sq hx0 hx1
  have hsecond : Real.transitionGapSecondDerivative x = R * E ^ 2 := by
    change Real.transitionGapSecondDerivative x = R * E ^ 2
    have hdivision : R = Real.transitionGapSecondDerivative x / E ^ 2 := hratio
    have hmultiply := congrArg (fun value : ℝ => value * E ^ 2) hdivision
    exact Eq.trans
      (Eq.trans
        (div_mul_cancel₀ (Real.transitionGapSecondDerivative x) henergyNe).symm
        hmultiply.symm)
      rfl
  have hexpanded := Real.transitionLogisticSecondDerivative_eq_expanded x
  unfold Real.transitionLogisticPositiveFactor
  unfold Real.transitionLogisticCurvatureBracket
  change Real.transitionLogisticSecondDerivative x =
    (e * u⁻¹ ^ 2 * E ^ 2) *
      (Real.exponentialOddRatio d - R)
  have hodd : Real.exponentialOddRatio d = (e - 1) / u := by
    exact Real.transitionConvexity_exponentialOddRatio_eq d
  have hfirstAssociation :
      e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 =
        (e * u⁻¹ ^ 2 * E ^ 2) * ((e - 1) / u) := by
    have hassociated :=
      Real.transitionConvexity_four_factor_association
        e (e - 1) u⁻¹ (E ^ 2)
    have hdivision : (e - 1) / u = (e - 1) * u⁻¹ :=
      div_eq_mul_inv (e - 1) u
    exact Eq.trans hassociated
      (congrArg
        (fun value : ℝ => (e * u⁻¹ ^ 2 * E ^ 2) * value)
        hdivision.symm)
  have hsecondAssociation :
      e * u⁻¹ ^ 2 * (R * E ^ 2) =
        (e * u⁻¹ ^ 2 * E ^ 2) * R := by
    exact Real.transitionConvexity_right_factor_commutation
      (e * u⁻¹ ^ 2) R (E ^ 2)
  exact Eq.trans hexpanded
    (Eq.trans
      (congrArg (fun value : ℝ =>
        e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 -
          e * u⁻¹ ^ 2 * value) hsecond)
      (by
        calc
          e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 -
              e * u⁻¹ ^ 2 * (R * E ^ 2) =
            (e * u⁻¹ ^ 2 * E ^ 2) * ((e - 1) / u) -
              (e * u⁻¹ ^ 2 * E ^ 2) * R := by
                exact congrArg₂ (fun first second : ℝ => first - second)
                  hfirstAssociation hsecondAssociation
          _ = (e * u⁻¹ ^ 2 * E ^ 2) *
              ((e - 1) / u - R) :=
            (mul_sub (e * u⁻¹ ^ 2 * E ^ 2) ((e - 1) / u) R).symm
          _ = (e * u⁻¹ ^ 2 * E ^ 2) *
              (Real.exponentialOddRatio d - R) :=
            congrArg (fun value : ℝ =>
              (e * u⁻¹ ^ 2 * E ^ 2) * (value - R)) hodd.symm))

theorem Real.smoothTransitionSecondDerivative_nonneg_of_pos_le_half
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    0 ≤ Real.smoothTransitionSecondDerivative x := by
  have hxOne : x < 1 := by
    have hhalfOne : (1 / 2 : ℝ) < 1 :=
      (div_lt_one zero_lt_two).mpr one_lt_two
    exact lt_of_le_of_lt hxHalf hhalfOne
  have hidentify :=
    Real.smoothTransitionSecondDerivative_eq_logisticSecond hx0 hxOne
  have hfactor := Real.transitionLogisticSecondDerivative_factorization hx0 hxOne
  have hprefactor := Real.transitionLogisticPositiveFactor_nonneg x
  have hbracket := Real.transitionLogisticCurvatureBracket_nonneg hx0 hxHalf
  exact Eq.subst (motive := fun value : ℝ => 0 ≤ value)
    (Eq.trans hidentify hfactor).symm
    (mul_nonneg hprefactor hbracket)

theorem Real.smoothTransitionSecondDerivative_nonneg_on_left_half
    (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    0 ≤ Real.smoothTransitionSecondDerivative x := by
  match lt_or_eq_of_le hx.1 with
  | Or.inl hxPos =>
      exact Real.smoothTransitionSecondDerivative_nonneg_of_pos_le_half
        hxPos hx.2
  | Or.inr hxZero =>
      have hzeroNonneg :
          0 ≤ Real.smoothTransitionSecondDerivative 0 :=
        le_of_eq Real.smoothTransitionSecondDerivative_zero.symm
      exact Eq.subst
        (motive := fun value : ℝ =>
          0 ≤ Real.smoothTransitionSecondDerivative value)
        hxZero
        hzeroNonneg

theorem Real.smoothTransitionSecondDerivative_nonpos_on_right_half
    (x : ℝ)
    (hx : x ∈ Set.Icc (1 / 2 : ℝ) 1) :
    Real.smoothTransitionSecondDerivative x ≤ 0 := by
  let y := 1 - x
  have hyNonneg : 0 ≤ y := sub_nonneg.mpr hx.2
  have hyHalf : y ≤ 1 / 2 := by
    have hreflectedBound : (1 : ℝ) - x ≤ 1 - 1 / 2 :=
      sub_le_sub_left hx.1 1
    have hhalfComplement : (1 : ℝ) - 1 / 2 = 1 / 2 :=
      Real.smoothTransition_half_complement
    exact le_trans hreflectedBound
      (le_of_eq hhalfComplement)
  have hyMem : y ∈ Set.Icc (0 : ℝ) (1 / 2) := ⟨hyNonneg, hyHalf⟩
  have hySign := Real.smoothTransitionSecondDerivative_nonneg_on_left_half y hyMem
  have hreflection := Real.smoothTransitionSecondDerivative_reflection_neg y
  have hinner : 1 - y = x := by
    unfold y
    exact Real.one_sub_one_sub x
  have hneg : -Real.smoothTransitionSecondDerivative y ≤ 0 :=
    neg_nonpos.mpr hySign
  exact Eq.subst
    (motive := fun value : ℝ =>
      Real.smoothTransitionSecondDerivative value ≤ 0)
    hinner
    (Eq.subst
      (motive := fun value : ℝ => value ≤ 0)
      hreflection.symm
      hneg)

theorem Real.integral_abs_smoothTransitionSecondDerivative_le_eight_closed :
    (∫ x in (0 : ℝ)..1,
      |Real.smoothTransitionSecondDerivative x|) ≤ 8 := by
  exact Real.integral_abs_smoothTransitionSecondDerivative_le_eight
    Real.smoothTransitionSecondDerivative_nonneg_on_left_half
    Real.smoothTransitionSecondDerivative_nonpos_on_right_half

end
end LFunctions
end Boundary
