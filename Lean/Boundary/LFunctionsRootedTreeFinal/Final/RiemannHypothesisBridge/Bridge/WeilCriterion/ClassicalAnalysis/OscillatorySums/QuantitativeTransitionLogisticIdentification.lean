import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.QuantitativeTransitionLogisticDerivatives

/-!
# Identification of the flat transition with its logistic coordinates

On the open unit interval, the normalized flat transition equals the
decreasing logistic of the reciprocal gap.  The equality is transported
through two derivative levels by local eventual equality.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.decreasingLogistic_transitionGap_eq_smoothTransition
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.decreasingLogistic (Real.transitionReciprocalGap x) =
      Real.smoothTransition x := by
  let A := expNegInvGlue x
  let B := expNegInvGlue (1 - x)
  have hA : 0 < A := expNegInvGlue.pos_of_pos hx0
  have hANe : A ≠ 0 := ne_of_gt hA
  have hratio := Real.exp_transitionReciprocalGap_eq_glue_ratio hx0 hx1
  unfold Real.decreasingLogistic
  unfold Real.smoothTransition
  change (1 + Real.exp (Real.transitionReciprocalGap x))⁻¹ = A / (A + B)
  have hdenominator :
      1 + Real.exp (Real.transitionReciprocalGap x) =
        (A + B) / A := by
    calc
      1 + Real.exp (Real.transitionReciprocalGap x) = 1 + B / A :=
        congrArg (fun value : ℝ => 1 + value) hratio
      _ = A / A + B / A :=
        congrArg (fun value : ℝ => value + B / A) (div_self hANe).symm
      _ = (A + B) / A := (add_div A B A).symm
  have hinverse : ((A + B) / A)⁻¹ = A / (A + B) := by
    exact inv_div (A + B) A
  exact Eq.trans
    (congrArg Inv.inv hdenominator)
    hinverse

theorem Real.smoothTransition_eq_decreasingLogistic_transitionGap
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.smoothTransition x =
      Real.decreasingLogistic (Real.transitionReciprocalGap x) := by
  exact (Real.decreasingLogistic_transitionGap_eq_smoothTransition hx0 hx1).symm

theorem Real.eventually_smoothTransition_eq_logistic
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.smoothTransition =ᶠ[nhds x]
      (fun y : ℝ =>
        Real.decreasingLogistic (Real.transitionReciprocalGap y)) := by
  have hneighborhood : Set.Ioo (0 : ℝ) 1 ∈ nhds x :=
    Ioo_mem_nhds hx0 hx1
  exact Filter.mem_of_superset hneighborhood
    (fun y hy =>
      Real.smoothTransition_eq_decreasingLogistic_transitionGap hy.1 hy.2)

theorem Real.hasDerivAt_smoothTransition_logistic
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasDerivAt Real.smoothTransition
      (Real.transitionLogisticFirstDerivative x) x := by
  have hxNe : x ≠ 0 := ne_of_gt hx0
  have hcompNe : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hlogistic :=
    Real.hasDerivAt_transitionLogisticComposite hxNe hcompNe
  have heq := Real.eventually_smoothTransition_eq_logistic hx0 hx1
  exact hlogistic.congr_of_eventuallyEq heq

theorem Real.smoothTransitionDerivative_eq_logisticFirst
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.smoothTransitionDerivative x =
      Real.transitionLogisticFirstDerivative x := by
  have hsmooth := Real.hasDerivAt_smoothTransition_logistic hx0 hx1
  have hexisting := Real.hasDerivAt_smoothTransition_exact x
  exact hexisting.unique hsmooth

theorem Real.eventually_smoothTransitionDerivative_eq_logisticFirst
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.smoothTransitionDerivative =ᶠ[nhds x]
      Real.transitionLogisticFirstDerivative := by
  have hneighborhood : Set.Ioo (0 : ℝ) 1 ∈ nhds x :=
    Ioo_mem_nhds hx0 hx1
  exact Filter.mem_of_superset hneighborhood
    (fun y hy =>
      Real.smoothTransitionDerivative_eq_logisticFirst hy.1 hy.2)

theorem Real.hasDerivAt_smoothTransitionDerivative_logistic
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasDerivAt Real.smoothTransitionDerivative
      (Real.transitionLogisticSecondDerivative x) x := by
  have hxNe : x ≠ 0 := ne_of_gt hx0
  have hcompNe : 1 - x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hlogistic :=
    Real.hasDerivAt_transitionLogisticFirstDerivative hxNe hcompNe
  have heq :=
    Real.eventually_smoothTransitionDerivative_eq_logisticFirst hx0 hx1
  exact hlogistic.congr_of_eventuallyEq heq

theorem Real.smoothTransitionSecondDerivative_eq_logisticSecond
    {x : ℝ}
    (hx0 : 0 < x)
    (hx1 : x < 1) :
    Real.smoothTransitionSecondDerivative x =
      Real.transitionLogisticSecondDerivative x := by
  have hlogistic :=
    Real.hasDerivAt_smoothTransitionDerivative_logistic hx0 hx1
  have hexisting := Real.hasDerivAt_smoothTransitionDerivative x
  exact hexisting.unique hlogistic

theorem Real.transitionLogisticSecondDerivative_eq_expanded
    (x : ℝ) :
    Real.transitionLogisticSecondDerivative x =
      Real.exp (Real.transitionReciprocalGap x) *
          (Real.exp (Real.transitionReciprocalGap x) - 1) *
          (1 + Real.exp (Real.transitionReciprocalGap x))⁻¹ ^ 3 *
          Real.transitionReciprocalEnergy x ^ 2 -
          Real.exp (Real.transitionReciprocalGap x) *
          (1 + Real.exp (Real.transitionReciprocalGap x))⁻¹ ^ 2 *
          Real.transitionGapSecondDerivative x := by
  let d := Real.transitionReciprocalGap x
  let e := Real.exp d
  let u := 1 + e
  let E := Real.transitionReciprocalEnergy x
  let S := Real.transitionGapSecondDerivative x
  change
    e * (e - 1) * u⁻¹ ^ 3 * (-E) ^ 2 +
        (-(e * u⁻¹ ^ 2)) * S =
      e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 -
        e * u⁻¹ ^ 2 * S
  have hnegativeSquare :
      (-E) ^ 2 = E ^ 2 := by
    exact Eq.trans
      (pow_two (-E))
      (Eq.trans
        (neg_mul_neg E E)
        (pow_two E).symm)
  have hfirstTerm :
      e * (e - 1) * u⁻¹ ^ 3 * (-E) ^ 2 =
        e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 :=
    congrArg
      (fun value : ℝ => e * (e - 1) * u⁻¹ ^ 3 * value)
      hnegativeSquare
  have hsecondTerm :
      (-(e * u⁻¹ ^ 2)) * S = -(e * u⁻¹ ^ 2 * S) :=
    neg_mul (e * u⁻¹ ^ 2) S
  have hadditiveForm :
      e * (e - 1) * u⁻¹ ^ 3 * (-E) ^ 2 +
          (-(e * u⁻¹ ^ 2)) * S =
        e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 +
          (-(e * u⁻¹ ^ 2 * S)) :=
    congrArg₂ (fun first second : ℝ => first + second)
      hfirstTerm hsecondTerm
  have hsubtractionForm :
      e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 +
          (-(e * u⁻¹ ^ 2 * S)) =
        e * (e - 1) * u⁻¹ ^ 3 * E ^ 2 -
          e * u⁻¹ ^ 2 * S :=
    (sub_eq_add_neg
      (e * (e - 1) * u⁻¹ ^ 3 * E ^ 2)
      (e * u⁻¹ ^ 2 * S)).symm
  exact Eq.trans hadditiveForm hsubtractionForm

def Real.transitionLogisticPositiveFactor (x : ℝ) : ℝ :=
  Real.exp (Real.transitionReciprocalGap x) *
    (1 + Real.exp (Real.transitionReciprocalGap x))⁻¹ ^ 2 *
    Real.transitionReciprocalEnergy x ^ 2

def Real.transitionLogisticCurvatureBracket (x : ℝ) : ℝ :=
  Real.exponentialOddRatio (Real.transitionReciprocalGap x) -
    Real.transitionScalarCurvatureRatio
      (Real.transitionReciprocalSum x)
      (Real.transitionReciprocalGap x)

theorem Real.transitionLogisticPositiveFactor_nonneg
    (x : ℝ) :
    0 ≤ Real.transitionLogisticPositiveFactor x := by
  unfold Real.transitionLogisticPositiveFactor
  have hexp : 0 ≤ Real.exp (Real.transitionReciprocalGap x) :=
    le_of_lt (Real.exp_pos _)
  have hinverse : 0 ≤
      (1 + Real.exp (Real.transitionReciprocalGap x))⁻¹ ^ 2 :=
    pow_nonneg (inv_nonneg.mpr
      (add_nonneg zero_le_one (le_of_lt (Real.exp_pos _)))) 2
  have henergy : 0 ≤ Real.transitionReciprocalEnergy x ^ 2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg hexp hinverse) henergy

theorem Real.transitionLogisticCurvatureBracket_nonneg
    {x : ℝ}
    (hx0 : 0 < x)
    (hxHalf : x ≤ 1 / 2) :
    0 ≤ Real.transitionLogisticCurvatureBracket x := by
  unfold Real.transitionLogisticCurvatureBracket
  exact sub_nonneg.mpr
    (Real.transitionCoordinateCurvatureRatio_le_exponential hx0 hxHalf)

end
end LFunctions
end Boundary
